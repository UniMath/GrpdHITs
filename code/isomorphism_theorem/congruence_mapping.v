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
Require Import hit_biadjunction.hit_prealgebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_algebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_algebra_biadj.
Require Import existence.initial_algebra.
Require Import isomorphism_theorem.congruence_relation.

Local Open Scope cat.

Definition idtoiso_path_groupoid
           {X : one_type}
           {x y : X}
           (p : x = y)
  : pr1 (@idtoiso (one_type_to_groupoid X) _ _ p) = p.
Proof.
  induction p ; apply idpath.
Defined.

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
                     fR a₁ a₂ g₁ @ fR a₂ a₃ g₂)
           (fRcommute : ∏ (x y : poly_act
                                   (point_constr Σ)
                                   (alg_carrier X))
                          (p : poly_act_rel
                                 (point_constr Σ)
                                 (cong_rel_carrier R)
                                 x y),
                        (fR (alg_constr X x) (alg_constr X y) (cong_rel_ops R x y p)
                         @ alg_map_commute f y
                         =
                         alg_map_commute f x
                         @ maponpaths (alg_constr Y) (poly_rel_to_eq_fun fR p)))
           (fRpath : ∏ (j : path_label Σ)
                       (x : poly_act (path_source Σ j) (alg_carrier X)),
                     sem_endpoint_UU_natural (path_left Σ j) (alg_map_commute f) x
                     @ alg_path Y j (poly_map (path_source Σ j) (alg_map_carrier f) x)
                     =
                     fR (sem_endpoint_UU (path_left Σ j) (alg_constr X) x)
                        (sem_endpoint_UU (path_right Σ j) (alg_constr X) x)
                        (make_groupoid_path_algebra_nat_trans_data R j x)
                     @ sem_endpoint_UU_natural (path_right Σ j) (alg_map_commute f) x).
  
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

  Definition factor_through_gquot_grpd_op_is_nat_trans_lem
             {P : poly_code}
             {x y : poly_act P (alg_carrier X)}
             (p : poly_act_rel P (cong_rel_carrier R) x y)
    : poly_rel_to_eq_fun fR p
      @ !(poly_path_groupoid_is_id (poly_map P (alg_map_carrier f) y))
      =
      !(poly_path_groupoid_is_id (poly_map P (alg_map_carrier f) x))
      @ # (poly_path_groupoid P (pr111 Y) : _ ⟶ _)
          (poly_act_functor_morphisms P factor_through_gquot_grpd_carrier p).
  Proof.
    simpl.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply pathscomp0rid.
    - apply pathscomp0rid.
    - induction x as [x | x], y as [y | y].
      + simpl.
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathsinv0 _ _)).
        }
        refine (!(maponpathscomp0 _ _ _) @ _).
        refine (maponpaths (maponpaths inl) (IHP₁ _ _ _) @ _).
        refine (maponpathscomp0 _ _ _ @ _).
        apply maponpaths_2.
        apply maponpathsinv0.
      + induction p.
      + induction p.
      + simpl.
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathsinv0 _ _)).
        }
        refine (!(maponpathscomp0 _ _ _) @ _).
        refine (maponpaths (maponpaths inr) (IHP₂ _ _ _) @ _).
        refine (maponpathscomp0 _ _ _ @ _).
        apply maponpaths_2.
        apply maponpathsinv0.
    - simpl.
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_inv.
      }
      refine (pathsdirprod_concat _ _ _ _ @ _).
      refine (paths_pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _) @ _).
      refine (!(pathsdirprod_concat _ _ _ _) @ _).
      apply maponpaths_2.
      refine (!_).
      apply pathsdirprod_inv.
  Qed.        
  
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
    refine (!_).
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (fRcommute _ _ p).
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!(maponpathscomp0 (alg_constr Y) _ _) @ _).
    apply maponpaths.
    exact (factor_through_gquot_grpd_op_is_nat_trans_lem p).
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

  Definition factor_through_gquot_grod_preserves_path_help
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (alg_carrier X))
    : poly_act_compose
        (sem_endpoint_grpd_natural_data
           e
           factor_through_gquot_grpd_prealg
           x)
        (poly_act_morphism_to_path
           (path_groupoid_endpoint
              e
              (poly_map P (alg_map_carrier f) x)))
      =
      @poly_act_morphism_to_path
        Q
        (pr111 (hit_algebra_biadjunction Σ Y))
        _ _
        (sem_endpoint_UU_natural
           e
           (alg_map_commute f)
           x).
  Proof.
    simpl.
    induction e as [P | P Q Q' e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q Q' e₁ IHe₁ e₂ IHe₂
                    | P T t | Z₁ Z₂ g | ].
    - apply poly_act_id_left.
    - simpl.
      refine (_ @ poly_act_compose_poly_act_morphism_to_path _ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!(IHe₂ _)).
      }
      clear IHe₂.
      refine (!(poly_act_assoc _ _ _) @ _).
      refine (_ @ poly_act_assoc _ _ _).
      apply maponpaths.
      refine (poly_act_compose_poly_act_morphism_to_path _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply homotsec_natural'.
      }
      refine (!(poly_act_compose_poly_act_morphism_to_path _ _) @ _).
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply homotsec_natural'.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply poly_act_compose_poly_act_morphism_to_path.
      }
      refine (poly_act_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply poly_path_groupoid_poly_act_morphism_to_path.
      }
      refine (_ @ poly_path_groupoid_poly_act_morphism_to_path _ _ _).
      etrans.
      {
        refine (!_).
        apply (functor_comp
                 (sem_endpoint_grpd
                    e₂
                    (_ ,, prealg_path_groupoid_map (point_constr Σ) (pr111 Y) (pr211 Y)))).
      }
      apply maponpaths.
      apply IHe₁.
    - apply poly_act_id_left.
    - apply poly_act_id_left.
    - apply poly_act_id_left.
    - apply poly_act_id_left.
    - simpl.
      apply pathsdirprod.
      + refine (_ @ IHe₁ _ @ _).
        * do 2 apply maponpaths.
          apply maponpaths_pr1_pathsdirprod.
        * apply maponpaths.
          refine (!_).
          apply maponpaths_pr1_pathsdirprod.
      + refine (_ @ IHe₂ _ @ _).
        * do 2 apply maponpaths.
          apply maponpaths_pr2_pathsdirprod.
        * apply maponpaths.
          refine (!_).
          apply maponpaths_pr2_pathsdirprod.
    - apply idpath.
    - apply idpath.
    - simpl ; unfold factor_through_gquot_grpd_op_data.
      refine (_ @ !(idtoiso_path_groupoid _)).
      etrans.
      {
        apply maponpaths.
        apply idtoiso_path_groupoid.
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathsinv0.
        }
        apply pathsinv0l.
      }
      apply pathscomp0rid.
  Qed.

  Definition factor_through_gquot_grod_preserves_path_help'
             {P : poly_code}
             (e : endpoint (point_constr Σ) P I)
             (x : poly_act P (alg_carrier X))
    : sem_endpoint_grpd_natural_data
        e
        factor_through_gquot_grpd_prealg
        x
      @ path_groupoid_endpoint
          e
          (poly_map P (alg_map_carrier f) x)
      =
      sem_endpoint_UU_natural
        e
        (alg_map_commute f)
        x.
  Proof.
    pose (factor_through_gquot_grod_preserves_path_help e x) as p.
    refine (_ @ p @ idtoiso_path_groupoid _).
    apply maponpaths.
    refine (!_).
    apply idtoiso_path_groupoid.
  Qed.
  
  Definition factor_through_gquot_grod_preserves_path
             (j : path_label Σ)
             (x : poly_act (path_source Σ j) (alg_carrier X))
    : fR
        (sem_endpoint_UU (path_left Σ j) (alg_constr X) x)
        (sem_endpoint_UU (path_right Σ j) (alg_constr X) x)
        (make_groupoid_path_algebra_nat_trans_data R j x)
      @ sem_endpoint_grpd_natural_data
          (path_right Σ j)
          factor_through_gquot_grpd_prealg
          x
      =
      sem_endpoint_grpd_natural_data
        (path_left Σ j)
        factor_through_gquot_grpd_prealg
        x
      @ path_groupoid_endpoint
          (path_left Σ j)
          (poly_map (path_source Σ j) (alg_map_carrier f) x)
      @ alg_path Y j (poly_map (path_source Σ j) (alg_map_carrier f) x)
      @ !(path_groupoid_endpoint
            (path_right Σ j)
            (poly_map (path_source Σ j) (alg_map_carrier f) x)).
  Proof.
    do 2 refine (_ @ !(path_assoc _ _ _)).
    use path_inv_rotate_rr.
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (factor_through_gquot_grod_preserves_path_help' (path_right Σ j) x).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (factor_through_gquot_grod_preserves_path_help' (path_left Σ j) x).
    }
    exact (fRpath j x).
  Qed.

  Definition factor_through_gquot_grpd
    : make_groupoid_algebra R
      -->
      hit_algebra_biadjunction Σ Y.
  Proof.
    use make_algebra_map_grpd.
    use make_hit_path_alg_map_grpd.
    - exact factor_through_gquot_grpd_prealg.
    - exact factor_through_gquot_grod_preserves_path.
  Defined.

  Definition factor_through_gquot
    : quotient_of_congruence R --> Y.
  Proof.
    use quotient_of_congruence_map.
    exact factor_through_gquot_grpd.
  Defined.

  Definition factor_through_gquot_gcl
             (x : alg_carrier X)
    : alg_map_carrier
        factor_through_gquot
        (gcl (make_groupoid_algebra_carrier R) x)
      =
      alg_map_carrier f x.
  Proof.
    apply idpath.
  Defined.

  Definition factor_through_gquot_gcleq
             {x y : alg_carrier X}
             (p : cong_rel_carrier R x y)
    : maponpaths
        (alg_map_carrier factor_through_gquot)
        (gcleq
           (make_groupoid_algebra_carrier R)
           p)
      =
      fR _ _ p.
  Proof.
    refine (!(maponpathscomp
                (gquot_functor_map factor_through_gquot_grpd_carrier)
                (gquot_counit_map (pr111 Y))
                (gcleq (make_groupoid_algebra_carrier R) p))
             @ _).
    etrans.
    {
      refine (maponpaths (maponpaths (gquot_counit_map (pr111 Y))) _).
      exact (gquot_rec_beta_gcleq (make_groupoid_algebra_carrier R) _ _ _ _ _ _ _ _ p).
    }
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  Qed.

  Definition factor_through_gquot_unique
             (g : quotient_of_congruence R --> Y)
             (eq_pt : ∏ (x : alg_carrier X),
                      alg_map_carrier g (gcl (make_groupoid_algebra_carrier R) x)
                      =
                      alg_map_carrier f x)
             (eq_path : ∏ (x y : alg_carrier X)
                          (p : cong_rel_carrier R x y),
                        maponpaths
                          (alg_map_carrier g)
                          (gcleq
                             (make_groupoid_algebra_carrier R)
                             p)
                        @ eq_pt y
                        =
                        eq_pt x @ fR _ _ p)
    : ∏ x, alg_map_carrier g x = alg_map_carrier factor_through_gquot x.
  Proof.
    use gquot_ind_set.
    - exact eq_pt.
    - abstract
        (intros a₁ a₂ x ;
         simpl ;
         apply map_PathOver ;
         unfold square ;
         specialize (eq_path a₁ a₂ x) ;
         refine (eq_path @ _) ;
         apply maponpaths ;
         refine (!_) ;
         apply factor_through_gquot_gcleq).
    - abstract
        (intros x y z ;
         exact (one_type_isofhlevel (pr111 Y) _ _ y z)).
  Defined.
End MapToQuotientFromCongruence.
