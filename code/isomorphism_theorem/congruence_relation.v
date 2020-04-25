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
Require Import hit_biadjunction.gquot_commute.
Require Import hit_biadjunction.gquot_natural.
Require Import hit_biadjunction.hit_algebra_biadj.lift_gquot.
Require Import hit_biadjunction.hit_path_algebra_biadj.lift_gquot.
Require Import hit_biadjunction.hit_path_algebra_biadj.counit.
Require Import hit_biadjunction.hit_path_algebra_biadj.unit.
Require Import hit_biadjunction.hit_algebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_algebra_biadj.
Require Import existence.initial_algebra.

Local Open Scope cat.

Section CongruenceRelation.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}.

  (** Definition of congruence relation *)
  Definition congruence_relation_groupoid
    : UU
    := ∑ (R : alg_carrier X → alg_carrier X → hSet), 
       ∑ (R_id : ∏ x : alg_carrier X, R x x), 
       ∑ (R_inv : ∏ x y : alg_carrier X, R x y → R y x), 
       ∑ (R_comp : ∏ x y z : alg_carrier X, R x y → R y z → R x z), 
       (∏ x y : alg_carrier X, ∏ r : R x y,
          R_comp x x y (R_id x) r = r)
       × 
       (∏ x y : alg_carrier X, ∏ r : R x y,
          R_comp x y y r (R_id y) = r)
       ×
       (∏ x y z w : alg_carrier X, ∏ r1 : R x y, ∏ r2 : R y z, ∏ r3 : R z w,
          R_comp x y w r1 (R_comp y z w r2 r3) = R_comp x z w (R_comp x y z r1 r2) r3)
       ×
       (∏ x y : alg_carrier X, ∏ r : R x y,
          R_comp y x y (R_inv x y r) r = R_id y)
       ×
       (∏ x y : alg_carrier X, ∏ r : R x y,
          R_comp x y x r (R_inv x y r) = R_id x).

  Definition make_congruence_relation_groupoid
             (R : alg_carrier X → alg_carrier X → UU)
             (Risaset : ∏ (x y : alg_carrier X), isaset (R x y))
             (R_id : ∏ (x : alg_carrier X), R x x) 
             (R_inv : ∏ (x y : alg_carrier X), R x y → R y x)
             (R_comp : ∏ (x y z : alg_carrier X), R x y → R y z → R x z)
             (R_idl : ∏ (x y : alg_carrier X) (r : R x y),
                      R_comp x x y (R_id x) r = r)
             (R_idr : ∏ (x y : alg_carrier X) (r : R x y),
                      R_comp x y y r (R_id y) = r)
             (R_assoc : ∏ (x y z w : alg_carrier X)
                          (r1 : R x y) (r2 : R y z) (r3 : R z w),
                        R_comp x y w r1 (R_comp y z w r2 r3)
                        =
                        R_comp x z w (R_comp x y z r1 r2) r3)
             (R_invl : ∏ (x y : alg_carrier X) (r : R x y),
                       R_comp y x y (R_inv x y r) r = R_id y)
             (R_invr : ∏ (x y : alg_carrier X) (r : R x y),
                       R_comp x y x r (R_inv x y r) = R_id x)
    : congruence_relation_groupoid
    := (λ x y, make_hSet (R x y) (Risaset x y))
       ,, R_id
       ,, R_inv
       ,, R_comp
       ,, R_idl
       ,, R_idr
       ,, R_assoc
       ,, R_invl
       ,, R_invr.
  
  (** Projections *)
  Section ProjectionsCarrier.
    Variable (R : congruence_relation_groupoid).

    Definition cong_rel_carrier : alg_carrier X → alg_carrier X → hSet
      := pr1 R.
    
    Definition cong_rel_id
               (x : alg_carrier X)
      : cong_rel_carrier x x
      := pr12 R x.

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
      : cong_rel_carrier y x
      := pr122 R x y r.

    Definition cong_rel_comp
               {x y z : alg_carrier X}
               (r1 : cong_rel_carrier x y)
               (r2 : cong_rel_carrier y z)
      : cong_rel_carrier x z
      := pr1 (pr222 R) x y z r1 r2.

    Definition cong_rel_lid
               {x y : alg_carrier X}
               (r : cong_rel_carrier x y)
      : cong_rel_comp (cong_rel_id x) r = r.
    Proof.
      exact (pr12 (pr222 R) x y r).      
    Qed.

    Definition cong_rel_rid
               {x y : alg_carrier X}
               (r : cong_rel_carrier x y)
      : cong_rel_comp r (cong_rel_id y) = r.
    Proof.
      exact (pr122 (pr222 R) x y r).      
    Qed.
    
    Definition cong_rel_assoc
               {x y z w : alg_carrier X}
               (r1 : cong_rel_carrier x y)
               (r2 : cong_rel_carrier y z)
               (r3 : cong_rel_carrier z w)
      : cong_rel_comp r1 (cong_rel_comp r2 r3)
        = cong_rel_comp (cong_rel_comp r1 r2) r3.
    Proof.
      exact (pr1 (pr222 (pr222 R)) x y z w r1 r2 r3).      
    Qed.

    Definition cong_rel_linv
               {x y : alg_carrier X}
               (r : cong_rel_carrier x y)
      : cong_rel_comp (cong_rel_inv r) r = cong_rel_id y.
    Proof.
      exact (pr12 (pr222 (pr222 R)) x y r).
    Qed.


    Definition cong_rel_rinv
               {x y : alg_carrier X}
               (r : cong_rel_carrier x y)
      : cong_rel_comp r (cong_rel_inv r) = cong_rel_id x.
    Proof.
      exact (pr22 (pr222 (pr222 R)) x y r).      
    Qed.
  End ProjectionsCarrier.

  Section MakeGroupoidFromCongruence.
    Variable (R : congruence_relation_groupoid).

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
  End MakeGroupoidFromCongruence.
  
  Definition is_congruence_relation_ops
             (R : congruence_relation_groupoid)
    : UU
    := ∑ (R_ops : ∏ x y : poly_act (point_constr Σ) (alg_carrier X),
            poly_act_rel (point_constr Σ) (pr1 R) x y →
            cong_rel_carrier R (alg_constr X x) (alg_constr X y)), 
       (∏ x : poly_act (point_constr Σ) (alg_carrier X),
          R_ops x x (poly_act_rel_identity _ _ (pr12 R) x)
          =
          pr12 R (alg_constr X x))
        × 
       (∏ x y z : poly_act (point_constr Σ) (alg_carrier X),
          ∏ (r1 : poly_act_rel (point_constr Σ) (pr1 R) x y),
          ∏ (r2 : poly_act_rel (point_constr Σ) (pr1 R) y z),
          R_ops x z
               (poly_act_rel_comp (point_constr Σ) _ (pr1 (pr222 R)) r1 r2)
          =
          pr1 (pr222 R) (alg_constr X x) (alg_constr X y) (alg_constr X z)
              (R_ops x y r1) (R_ops y z r2)).

  Definition congruence_relation_ops
    : UU
    := ∑ (R : congruence_relation_groupoid),
       is_congruence_relation_ops R.

  Definition make_congruence_relation_ops
             (R : congruence_relation_groupoid)
             (R_ops : ∏ (x y : poly_act (point_constr Σ) (alg_carrier X)),
                      poly_act_rel (point_constr Σ) (pr1 R) x y
                      →
                      cong_rel_carrier R (alg_constr X x) (alg_constr X y))
             (R_opsid : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
                        R_ops x x (poly_act_rel_identity _ _ (pr12 R) x)
                        =
                        pr12 R (alg_constr X x))
             (R_opscomp : (∏ (x y z : poly_act (point_constr Σ) (alg_carrier X))
                             (r1 : poly_act_rel (point_constr Σ) (pr1 R) x y)
                             (r2 : poly_act_rel (point_constr Σ) (pr1 R) y z),
                           R_ops
                             x z
                             (poly_act_rel_comp (point_constr Σ) _ (pr1 (pr222 R)) r1 r2)
                           =
                           pr1 (pr222 R)
                               (alg_constr X x) (alg_constr X y) (alg_constr X z)
                               (R_ops x y r1) (R_ops y z r2)))
    : congruence_relation_ops
    := (R ,, R_ops ,, R_opsid ,, R_opscomp).
             
  Definition congruence_relation_ops_to_congruence_relation_groupoid
    : congruence_relation_ops → congruence_relation_groupoid
    := λ z, pr1 z.

  Coercion congruence_relation_ops_to_congruence_relation_groupoid
    : congruence_relation_ops >-> congruence_relation_groupoid.
  
  (** Projections involving the operation (functor) *)
  Section ProjectionsOperation.
    Variable (R : congruence_relation_ops).

    Definition cong_rel_ops
               (x y : poly_act (point_constr Σ) (alg_carrier X))
               (r : poly_act_rel (point_constr Σ) (cong_rel_carrier R) x y)
      : cong_rel_carrier R (alg_constr X x) (alg_constr X y)
      := pr12 R x y r.

    Definition cong_rel_ops_idax
               (x : poly_act (point_constr Σ) (alg_carrier X))
      : cong_rel_ops x x (poly_act_rel_identity _ _ (cong_rel_id R) x)
        =
        cong_rel_id R (alg_constr X x).
    Proof.
      exact (pr122 R x).
    Qed.

    Definition cong_rel_ops_compax
               (x y z : poly_act (point_constr Σ) (alg_carrier X))
               (r1 : poly_act_rel (point_constr Σ) (cong_rel_carrier R) x y)
               (r2 : poly_act_rel (point_constr Σ) (cong_rel_carrier R) y z)
      : cong_rel_ops
          x z
          (poly_act_rel_comp
             (point_constr Σ)
             _
             (λ x y z r1 r2, cong_rel_comp R r1 r2) r1 r2)
        = cong_rel_comp
            R
            (cong_rel_ops x y r1)
            (cong_rel_ops y z r2).
    Proof.
      exact (pr222 R x y z r1 r2).
    Qed.
  End ProjectionsOperation.

  Section MakeGroupoidPrealgebraFromCongruence.
    Variable (R : congruence_relation_ops).
    
    Definition make_groupoid_algebra_operations_functor_data
      : functor_data
          (⦃ point_constr Σ ⦄ (make_groupoid_algebra_carrier R) : groupoid)
          (make_groupoid_algebra_carrier R).
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
      : (⦃ point_constr Σ ⦄ (make_groupoid_algebra_carrier R) : groupoid)
          ⟶
          make_groupoid_algebra_carrier R.
    Proof.
      use make_functor.
      - exact make_groupoid_algebra_operations_functor_data.
      - exact make_groupoid_algebra_operations_is_functor.
    Defined.

    Definition make_groupoid_prealgebra
      : hit_prealgebra_grpd Σ.
    Proof.
      use make_hit_prealgebra_grpd.
      - exact (make_groupoid_algebra_carrier R).
      - exact make_groupoid_algebra_operations.
    Defined.
  End MakeGroupoidPrealgebraFromCongruence.

  Definition is_congruence_relation_nat
             (R : congruence_relation_ops)
    := ∏ (j : path_label Σ)
         (x y : poly_act (path_source Σ j) (alg_carrier X))
         (f : poly_act_rel (path_source Σ j) (cong_rel_carrier R) x y),
       cong_rel_comp
         R
         (sem_endpoint_grpd_data_functor_morphism
            (path_left Σ j)
            (make_groupoid_algebra_operations R)
            f)
         (eq_to_cong_rel R (alg_path X j y))
       = cong_rel_comp
           R
           (eq_to_cong_rel R (alg_path X j x))
           (sem_endpoint_grpd_data_functor_morphism
              (path_right Σ j)
              (make_groupoid_algebra_operations R)
              f).
  
  Definition congruence_relation_nat
    : UU
    := ∑ (R : congruence_relation_ops),
       is_congruence_relation_nat R.

  Definition make_congruence_relation_nat
             (R : congruence_relation_ops)
             (R_nat :  is_congruence_relation_nat R)
    : congruence_relation_nat
    := R ,, R_nat.

  Definition congruence_relation_nat_to_congruence_relation_ops
    : congruence_relation_nat → congruence_relation_ops
    := λ z, pr1 z.

  Coercion congruence_relation_nat_to_congruence_relation_ops
    : congruence_relation_nat >-> congruence_relation_ops.
    
  Section ProjectionsNatTrans.
    Variable (R : congruence_relation_nat).

    Definition cong_rel_nat 
               (j : path_label Σ)
               (x y : poly_act (path_source Σ j) (alg_carrier X))
               (f : poly_act_rel (path_source Σ j) (cong_rel_carrier R) x y)
      : cong_rel_comp
          R
          (sem_endpoint_grpd_data_functor_morphism
             (path_left Σ j)
             (make_groupoid_algebra_operations R)
             f)
          (eq_to_cong_rel R (alg_path X j y))
        = cong_rel_comp
            R
            (eq_to_cong_rel R (alg_path X j x))
            (sem_endpoint_grpd_data_functor_morphism
               (path_right Σ j)
               (make_groupoid_algebra_operations R)
               f).
    Proof.
      exact (pr2 R j x y f).
    Qed.
  End ProjectionsNatTrans.

  Section MakeGroupoidPathalgebraFromCongruence.
    Variable (R : congruence_relation_nat).
  
    Definition make_groupoid_path_algebra_nat_trans_data
               (j : path_label Σ)
      : nat_trans_data
          (sem_endpoint_grpd_data_functor
             (path_left Σ j)
             (make_groupoid_prealgebra R))
          (sem_endpoint_grpd_data_functor
             (path_right Σ j)
             (make_groupoid_prealgebra R)).
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
      exact (cong_rel_nat R j).
    Qed.

    Definition make_groupoid_path_algebra_path
               (j : path_label Σ)
      : sem_endpoint_grpd_data_functor
          (path_left Σ j)
          (make_groupoid_prealgebra R)
        ⟹
        sem_endpoint_grpd_data_functor
          (path_right Σ j)
          (make_groupoid_prealgebra R).
    Proof.
      use make_nat_trans.
      - exact (make_groupoid_path_algebra_nat_trans_data j).
      - exact (make_groupoid_path_algebra_is_nat_trans j).
    Defined.

    Definition make_groupoid_path_algebra
      : hit_path_algebra_grpd Σ.
    Proof.
      use make_hit_path_algebra_grpd.
      - exact (make_groupoid_prealgebra R).
      - exact make_groupoid_path_algebra_path.
    Defined.
  End MakeGroupoidPathalgebraFromCongruence.

  Definition is_congruence_relation
             (R : congruence_relation_nat)
    : UU
    := ∏ (j : homot_label Σ)
         (x : poly_act (homot_point_arg Σ j) (pr111 (make_groupoid_path_algebra R)))
         (p : poly_act_rel
                (homot_path_arg_target Σ j)
                (cong_rel_carrier R)
                (sem_endpoint_UU
                   (homot_path_arg_left Σ j)
                   (alg_constr X)
                   x)
                (sem_endpoint_UU
                   (homot_path_arg_right Σ j)
                   (alg_constr X)
                   x)),
       sem_homot_endpoint_grpd
         (homot_left_path Σ j)
         (make_groupoid_prealgebra R)
         (make_groupoid_path_algebra_path R) x p
       =
       sem_homot_endpoint_grpd
         (homot_right_path Σ j)
         (make_groupoid_prealgebra R)
         (make_groupoid_path_algebra_path R) x p.

  Definition congruence_relation
    : UU
    := ∑ (R : congruence_relation_nat),
       is_congruence_relation R.

  Definition make_congruence_relation
             (R : congruence_relation_nat)
             (HR : is_congruence_relation R)
    : congruence_relation
    := R ,, HR.

  Definition congruence_relation_to_congruence_relation_nat
    : congruence_relation → congruence_relation_nat
    := λ z, pr1 z.

  Coercion congruence_relation_to_congruence_relation_nat
    : congruence_relation >-> congruence_relation_nat.
  
  Section ProjectionsIsAlgebra.
    Variable (R : congruence_relation).

    Definition cong_rel_is_alg_homot
               (j : homot_label Σ)
               (x : poly_act (homot_point_arg Σ j) (pr111 (make_groupoid_path_algebra R)))
               (p : poly_act_rel
                      (homot_path_arg_target Σ j)
                      (cong_rel_carrier R)
                      (sem_endpoint_UU
                         (homot_path_arg_left Σ j)
                         (alg_constr X)
                         x)
                      (sem_endpoint_UU
                         (homot_path_arg_right Σ j)
                         (alg_constr X)
                         x))
      : sem_homot_endpoint_grpd
          (homot_left_path Σ j)
          (make_groupoid_prealgebra R)
          (make_groupoid_path_algebra_path R) x p
        =
        sem_homot_endpoint_grpd
          (homot_right_path Σ j)
          (make_groupoid_prealgebra R)
          (make_groupoid_path_algebra_path R) x p.
    Proof.
      exact (pr2 R j x p).
    Qed.
  End ProjectionsIsAlgebra.
  
  Section MakeGroupoidAlgebraFromCongruence.
    Variable (R : congruence_relation).

    Definition make_groupoid_algebra_is_hit_algebra
      : is_hit_algebra_grpd Σ (make_groupoid_path_algebra R).
    Proof.
      exact (cong_rel_is_alg_homot R).
    Qed.
    
    Definition make_groupoid_algebra
      : hit_algebra_grpd Σ.
    Proof.
      use make_algebra_grpd.
      - exact (make_groupoid_path_algebra R).
      - exact make_groupoid_algebra_is_hit_algebra.
    Defined.
  End MakeGroupoidAlgebraFromCongruence.

  Definition quotient_of_congruence
             (R : congruence_relation)
    : hit_algebra_one_types Σ
    := _ ,, gquot_is_hit_algebra Σ _ (pr2 (make_groupoid_algebra R)).
End CongruenceRelation.

Arguments congruence_relation_groupoid {_} _ .
Arguments congruence_relation_ops {_} _ .
Arguments congruence_relation_nat {_} _.
Arguments congruence_relation {_} _.  

