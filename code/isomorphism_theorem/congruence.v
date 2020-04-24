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

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Definition poly_gquot_poly_map
           {P : poly_code}
           {G : groupoid}
           (x : poly_act P G)
  : gcl (poly_act_groupoid P G) (x)
    =
    poly_gquot
      P
      _
      (poly_map
         P
         (gcl G)
         x).
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths gquot_inl_grpd (IHP₁ x)).
    + exact (maponpaths gquot_inr_grpd (IHP₂ x)).
  - apply TODO.
Defined.


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
  Section ProjectionsCarrier.
    Variable (R : congruence_relation).

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

  Section MakeGroupoidFromCongruence.
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
  End MakeGroupoidFromCongruence.
  
  (** Projections involving the operation (functor) *)
  Section ProjectionsOperation.
    Variable (R : congruence_relation).

    Definition cong_rel_ops
               (x y : poly_act (point_constr Σ) (alg_carrier X))
               (r : poly_act_rel (point_constr Σ) (cong_rel_carrier R) x y)
    : cong_rel_carrier R (alg_constr X x) (alg_constr X y).
    Proof.
      apply TODO.
    Defined.

    Definition cong_rel_ops_idax
               (x : poly_act (point_constr Σ) (alg_carrier X))
      : cong_rel_ops x x (poly_act_rel_identity _ _ (cong_rel_id R) x)
        =
        cong_rel_id R (alg_constr X x).
    Proof.
      apply TODO.
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
      apply TODO.
    Qed.
  End ProjectionsOperation.

  Section MakeGroupoidPrealgebraFromCongruence.
    Variable (R : congruence_relation).
    
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
    
  Section MakeGroupoidPathalgebraFromCongruence.
    Variable (R : congruence_relation).
  
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
      intros x y f.
      simpl ; cbn ; cbn in x, y, f
      ; unfold make_groupoid_path_algebra_nat_trans_data.
      apply TODO.
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

  Section MakeGroupoidAlgebraFromCongruence.
    Variable (R : congruence_relation).

    Definition make_groupoid_algebra_is_hit_algebra
      : is_hit_algebra_grpd Σ (make_groupoid_path_algebra R).
    Proof.
      intros j x p.
      cbn in p.
      pose (alg_homot X j x) as q.
      cbn.
      cbn in q.
      unfold sem_homot_endpoint_one_types in q.
      unfold poly_act_morphism in p.
      cbn in p.
      apply TODO.
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

  (** Inclusion from `X` into the quotient of `R` *)
  Section MapToCongruence.
    Variable (R : congruence_relation).

    Definition congruence_gcl_map
      : alg_carrier X → alg_carrier (quotient_of_congruence R)
      := gcl (make_groupoid_algebra_carrier R).

    Definition congruence_gcl_preserves_point
      : preserves_point congruence_gcl_map
      := λ x,
         maponpaths
           (gquot_functor_map
              (make_groupoid_algebra_operations R))
           (@poly_gquot_poly_map
              _
              (alg_carrier_grpd (make_groupoid_algebra R))
              x).

    Definition congruence_gcl_prealg
      : pr11 X --> pr11 (quotient_of_congruence R).
    Proof.
      use one_types_homotopies.make_hit_prealgebra_mor.
      - exact congruence_gcl_map.
      - exact congruence_gcl_preserves_point.
    Defined.

    Definition lem
               {P Q : poly_code}
               (e : endpoint (point_constr Σ) P Q)
               (x : poly_act P (alg_carrier X))
      : sem_endpoint_UU_natural e congruence_gcl_preserves_point x
        =
        @poly_map_gcl_is_gquot_poly
          Q
          (make_groupoid_algebra_carrier R)
          (sem_endpoint_UU e prealg_constr x)
        @ !(gquot_endpoint_help
              e
              (gcl (poly_act_groupoid P (pr1 (make_groupoid_prealgebra R))) x))
        @ maponpaths
            _
            (maponpaths
               gquot_poly
               (poly_gquot_poly_map _)
             @ gquot_poly_poly_gquot
                 (poly_map P (gcl (make_groupoid_algebra_carrier R)) x)).
    Proof.
      induction e as [P | P Q Q' e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q
                      | P Q Q' e₁ IHe₁ e₂ IHe₂
                      | P T t | Z₁ Z₂ g | ].
      - simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpathsidfun.
        }
        apply TODO.
      - apply TODO.
      - simpl.
        refine (!_).
        refine (!(maponpathscomp0 inl _ _) @ _ @ maponpaths_idpath).
        apply maponpaths.
        apply TODO.
      - simpl.
        refine (!_).
        refine (!(maponpathscomp0 inr _ _) @ _ @ maponpaths_idpath).
        apply maponpaths.
        apply TODO.
      - apply TODO.
      - apply TODO.
      - simpl.
        refine (paths_pathsdirprod (IHe₁ _) (IHe₂ _) @ _).
        refine (!(pathsdirprod_concat _ _ _ _) @ _).
        apply maponpaths.
        refine (!(pathsdirprod_concat _ _ _ _) @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply pathsdirprod_inv.
        }
        apply maponpaths.
        refine (!_).
        apply maponpaths_prod_path.
      - simpl.
        refine (!_).
        apply maponpaths_for_constant_function.
      - apply idpath.
      - apply TODO.
    Qed.        

    Definition gcl_sem_endpoint_UU_natural
               {P : poly_code}
               (e : endpoint (point_constr Σ) P I)
               (x : poly_act P (alg_carrier X))
      : sem_endpoint_UU_natural e congruence_gcl_preserves_point x
        =
        maponpaths
          gquot_poly
          (maponpaths
             (gquot_functor_map (sem_endpoint_grpd e (make_groupoid_prealgebra R)))
             (@poly_gquot_poly_map P (make_groupoid_algebra_carrier R) x))
        @ !(@gquot_endpoint
              _ _ _
              e
              (make_groupoid_prealgebra R)
              (poly_map P (gcl (make_groupoid_algebra_carrier R)) x)).
    Proof.
      unfold gquot_endpoint.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply pathscomp_inv.
      }
      refine (path_assoc _ _ _ @ _).
      use path_inv_rotate_lr.
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          exact (maponpathscomp
                   (gquot_functor_map
                      (sem_endpoint_grpd e (make_groupoid_prealgebra R)))
                   gquot_poly
                   (poly_gquot_poly_map _)).
        }
        unfold funcomp.
        exact (@homotsec_natural'
                 _ _ _ _
                 (invhomot (@gquot_endpoint_help _ _ _ e (make_groupoid_prealgebra R)))
                 _ _
                 (@poly_gquot_poly_map P (make_groupoid_algebra_carrier R) x)).
      }
      unfold invhomot.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathscomp.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpathsinv0.
      }
      use path_inv_rotate_lr.
      refine (!_).
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathscomp0.
      }
      refine (!_).
      exact (lem e x).
    Qed.

    Definition maponpaths_gcl_eq_to_cong_rel
               {x₁ x₂ : alg_carrier X}
               (p : x₁ = x₂)
      : gcleq
          (make_groupoid_algebra_carrier R)
          (eq_to_cong_rel R p)
        =
        maponpaths
          (gcl (make_groupoid_algebra_carrier R))
          p.
    Proof.
      induction p ; simpl.
      apply ge.
    Qed.
    
    Definition congruence_gcl_preserves_path
      : preserves_path _ (prealg_map_commute congruence_gcl_prealg).
    Proof.
      intros i x.
      cbn.
      unfold lift_gquot_add2cell_obj, congruence_gcl_map.
      etrans.
      {
        apply maponpaths.
        pose (gcl_sem_endpoint_UU_natural (path_right Σ i) x) as p.
        refine (p @ _).
        apply pathscomp0lid.
      }
      refine (path_assoc _ _ _ @ _).
      do 2 refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          pose (gcl_sem_endpoint_UU_natural (path_left Σ i) x) as p.
          refine (p @ _).
          apply pathscomp0lid.
        }
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          apply pathsinv0l.
        }
        apply pathscomp0rid.
      }
      etrans.
      {
        refine (!_).
        exact (maponpathscomp0
                 gquot_poly
                 (maponpaths
                    (gquot_functor_map
                       (sem_endpoint_grpd
                          (path_left Σ i)
                          (make_groupoid_prealgebra R)))
                    (poly_gquot_poly_map _))
                 _).
      }
      etrans.
      {
        apply maponpaths.
        apply homotsec_natural'.
      }
      simpl.
      etrans.
      {
        exact (maponpathscomp0
                 (gquot_id _)
                 (gcleq
                    (poly_act_groupoid I (make_groupoid_algebra_carrier R))
                    (make_groupoid_path_algebra_nat_trans_data R i x))
                 _).
      }
      apply maponpaths_2.
      etrans.
      {
        apply gquot_rec_beta_gcleq.
      }
      apply maponpaths_gcl_eq_to_cong_rel.
    Qed.
        
    Definition congruence_gcl
      : X --> quotient_of_congruence R.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - exact congruence_gcl_prealg.
      - exact congruence_gcl_preserves_path.
    Defined.
  End MapToCongruence.

  (** Mapping principle for the quotient *)
  Section MapToQuotientFromCongruence.
    Context (R : congruence_relation)
            (Y : hit_algebra_one_types Σ)
            (F : make_groupoid_algebra R
                 -->
                 hit_algebra_biadjunction Σ Y).

    Definition quotient_of_congruence_map
      : quotient_of_congruence R --> Y
      := biadj_left_hom
           (hit_algebra_biadjunction Σ)
           (make_groupoid_algebra R)
           Y
           F.

  End MapToQuotientFromCongruence.

  Section MakeMapToQuotientFromCongruence.
    Variable (R : congruence_relation)
             (Y : hit_algebra_one_types Σ).

    Variable (f : alg_carrier X → alg_carrier Y)
             (fR : ∏ (a b : alg_carrier X),
                   cong_rel_carrier R a b → f a = f b).

    Definition test_prealg_carrier_data
      : functor_data
          (alg_carrier_grpd (make_groupoid_algebra R))
          (alg_carrier_grpd (hit_algebra_biadjunction Σ Y)).
    Proof.
      use make_functor_data.
      - exact f.
      - exact fR.
    Defined.

    Definition test_prealg_carrier_is_functor
      : is_functor test_prealg_carrier_data.
    Proof.
      apply TODO.
    Qed.
    
    Definition test_prealg_carrier
      : alg_carrier_grpd (make_groupoid_algebra R)
        ⟶
        alg_carrier_grpd (hit_algebra_biadjunction Σ Y).
    Proof.
      use make_functor.
      - exact test_prealg_carrier_data.
      - exact test_prealg_carrier_is_functor.
    Defined.

    Definition test_prealg
      : pr11 (make_groupoid_algebra R) --> pr11 (hit_algebra_biadjunction Σ Y).
    Proof.
      use make_hit_prealgebra_mor.
      - exact test_prealg_carrier.
      - apply TODO.
    Defined.

    Definition test
      : make_groupoid_algebra R
        -->
        hit_algebra_biadjunction Σ Y.
    Proof.
      use make_algebra_map_grpd.
      use make_hit_path_alg_map_grpd.
      - exact test_prealg.
      - apply TODO.
    Defined.

    Definition test_map
      : quotient_of_congruence R --> Y.
    Proof.
      use quotient_of_congruence_map.
      exact test.
    Defined.
  End MakeMapToQuotientFromCongruence.
End CongruenceRelation.
