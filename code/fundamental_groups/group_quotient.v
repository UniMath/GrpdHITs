(**
We determine the path space of the group quotient
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
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
Require Import displayed_algebras.displayed_algebra.
Require Import initial_grpd_alg.W_poly.
Require Import initial_grpd_alg.initial_groupoid_algebra.
Require Import initial_grpd_alg.is_initial.
Require Import existence.hit_existence.
Require Import examples.group_quotient.

Require Import fundamental_groups.loops.

Local Open Scope cat.


(**
Initial groupoid algebra for the group quotient constructed in a special way.
 *)
Section GroupQuotient.
  Variable (G : gr).

  Definition group_quot_initial_algebra_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact unit. 
      + exact (λ _ _, G).
    - exact (λ _, unel G).
    - exact (λ _ _ _, op).
  Defined.

  Definition group_quot_initial_algebra_is_precategory
    : is_precategory group_quot_initial_algebra_precategory_data.
  Proof.
    use make_is_precategory.
    - exact (λ _ _, lunax G).
    - exact (λ _ _, runax G).
    - exact (λ _ _ _ _ x y z, ! assocax G x y z). 
    - exact (λ _ _ _ _, assocax G).
  Qed.

  Definition group_quot_initial_algebra_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact group_quot_initial_algebra_precategory_data.
    - exact group_quot_initial_algebra_is_precategory.
  Defined.

  Definition group_quot_initial_algebra_homsets
    : has_homsets group_quot_initial_algebra_precategory.
  Proof.
    intros x y.
    apply (pr11 G).
  Qed.

  Definition group_quot_initial_algebra_category
    : category.
  Proof.
    use make_category.
    - exact group_quot_initial_algebra_precategory.
    - exact group_quot_initial_algebra_homsets.
  Defined.

  Definition group_quot_initial_algebra_is_pregroupoid
    : is_pregroupoid group_quot_initial_algebra_category.
  Proof.
    intros ? ? x.
    use make_is_z_isomorphism.
    - exact (grinv G x).
    - split.
      + exact (grrinvax G x).
      + exact (grlinvax G x).
  Defined.

  Definition group_quot_initial_algebra_carrier
    : groupoid.
  Proof.
    use make_groupoid.
    - exact group_quot_initial_algebra_category.
    - exact group_quot_initial_algebra_is_pregroupoid.
  Defined.

  (** It forms a groupoid algebra *)
  Definition group_quot_initial_algebra_base_data
    : functor_data
        (⦃ point_constr (group_quot_signature G) ⦄ group_quot_initial_algebra_carrier : groupoid)
        (group_quot_initial_algebra_carrier).
  Proof.
    use make_functor_data.
    - exact (λ x, x).
    - exact (λ _ _ _, unel G).
  Defined.

  Definition group_quot_initial_algebra_base_is_functor
    : is_functor group_quot_initial_algebra_base_data.
  Proof.
    split.
    - exact (λ _, idpath _).
    - exact (λ _ _ _ _ _, ! runax G  _).
  Qed.

  Definition group_quot_initial_algebra_base
    : (⦃ point_constr (group_quot_signature G) ⦄ group_quot_initial_algebra_carrier : groupoid)
        ⟶
        group_quot_initial_algebra_carrier.
  Proof.
    use make_functor.
    - exact group_quot_initial_algebra_base_data.
    - exact group_quot_initial_algebra_base_is_functor.
  Defined.

  Definition group_quot_initial_prealgebra
    : hit_prealgebra_grpd (group_quot_signature G).
  Proof.
    use make_hit_prealgebra_grpd.
    - exact group_quot_initial_algebra_carrier.
    - exact group_quot_initial_algebra_base.
  Defined.

  Definition group_quot_initial_algebra_loop
    : sem_endpoint_grpd_data_functor_data
        (group_quot_base_ep (group_quot_path_arg G tt))
        group_quot_initial_prealgebra
        ⟹
        sem_endpoint_grpd_data_functor_data
        (group_quot_base_ep (group_quot_path_arg G tt))
        group_quot_initial_prealgebra.
  Proof.
    use make_nat_trans.
    - exact (λ x, x). 
    - intros x y eq.
      exact (lunax G y @ ! eq @ ! runax G x).
  Defined.

  Definition group_quot_initial_path_algebra
    : hit_path_algebra_grpd (group_quot_signature G).
  Proof.
    use make_hit_path_algebra_grpd.
    - exact group_quot_initial_prealgebra.
    - exact (λ _, group_quot_initial_algebra_loop).
  Defined.

  Definition group_quot_initial_is_hit_algebra
    : is_hit_algebra_grpd
        (group_quot_signature G)
        group_quot_initial_path_algebra.
  Proof.
    intros j x ?.
    induction j.
    - simpl; cbn.
      rewrite !(lunax G _).
      rewrite (grlinvax G _).
      apply idpath.
    - simpl ; cbn.
      rewrite (grrinvax G).
      rewrite !(lunax G _).
      rewrite !(runax G _).
      apply idpath.
  Qed.  

  Definition group_quot_initial_algebra
    : hit_algebra_grpd (group_quot_signature G).
  Proof.
    use make_algebra_grpd.
    - exact group_quot_initial_path_algebra.
    - exact group_quot_initial_is_hit_algebra.
  Defined.

  (** The UMP for 1-cells *)

  Section GroupQuotInitialAlgUMPOne.
    Variable (H : hit_algebra_grpd (group_quot_signature G)).

    Local Notation "'Hmor'" := (alg_path_grpd H tt).

    Definition group_quot_initial_algebra_ump_1_carrier_data_0
      : alg_carrier_grpd H
      := alg_constr_grpd H tt.


    Definition group_quot_initial_algebra_ump_1_carrier_data_1
               (x : G)
      : alg_carrier_grpd H ⟦ group_quot_initial_algebra_ump_1_carrier_data_0 ,
                             group_quot_initial_algebra_ump_1_carrier_data_0 ⟧
      := Hmor x.

    Definition group_quot_initial_algebra_ump_1_carrier_data
      : functor_data
          group_quot_initial_algebra_precategory_data
          (alg_carrier_grpd H).
    Proof.
      use make_functor_data.
      - exact (λ _, group_quot_initial_algebra_ump_1_carrier_data_0).
      - exact (λ _ _, group_quot_initial_algebra_ump_1_carrier_data_1). 
    Defined.

    Definition group_quot_initial_algebra_ump_1_carrier_functor_id
      : Hmor 1%multmonoid = id₁ (alg_constr_grpd H tt).
    Proof.
      refine (! id_left _ @ _ @ alg_homot_grpd H group_quot_ident tt (idpath _)).
      simpl.
      rewrite (functor_id (pr211 H)).
      repeat rewrite id_left.
      repeat rewrite id_right.
      refine (maponpaths (λ z, z · Hmor _) (!_ @ id_right _)).
      use z_iso_inv_on_right.
      exact (! id_right _).
    Qed.
    
    Definition group_quot_initial_algebra_ump_1_carrier_is_functor
      : is_functor group_quot_initial_algebra_ump_1_carrier_data.
    Proof.
      split.
      - exact (λ _, group_quot_initial_algebra_ump_1_carrier_functor_id).      
      - intros ? ? ? x y.
        simpl.
        refine (!_ @ alg_homot_grpd H group_quot_comp (x ,, y) (idpath _) @ _).
        + simpl.
          rewrite (functor_id (pr211 H)).
          repeat rewrite id_left.
          repeat rewrite id_right.
          use z_iso_inv_on_right.
          rewrite id_left.
          exact (idpath _).
        + simpl.
          rewrite (functor_id (pr211 H)).
          repeat rewrite id_left.
          repeat rewrite id_right.
          etrans.
          {
            apply maponpaths.
            use z_iso_inv_on_right.
            rewrite id_left.
            exact (idpath _).
          }
          apply maponpaths_2.
          use z_iso_inv_on_right.
          rewrite id_left.
          exact (idpath _).
    Qed.

    Definition group_quot_initial_algebra_ump_1_carrier
      : group_quot_initial_algebra_carrier ⟶ alg_carrier_grpd H.
    Proof.
      use make_functor.
      - exact group_quot_initial_algebra_ump_1_carrier_data.
      - exact group_quot_initial_algebra_ump_1_carrier_is_functor.
    Defined.

    Definition group_quot_initial_algebra_ump_1_commute_data
      : nat_trans_data
          (functor_composite_data
             group_quot_initial_algebra_base_data
             group_quot_initial_algebra_ump_1_carrier_data)
          (functor_composite_data
             (poly_act_functor
                group_quot_point_constr
                group_quot_initial_algebra_ump_1_carrier)
             (alg_constr_grpd H)).
    Proof.
      intros x.
      induction x ; simpl.
      apply id₁.
    Defined.

    Definition group_quot_initial_algebra_ump_1_commute_is_nat_trans
      : is_nat_trans
          _ _
          group_quot_initial_algebra_ump_1_commute_data.
    Proof.
      intros x y f.
      induction x, y.
      simpl.
      rewrite !id_left.
      rewrite !id_right.
      unfold group_quot_initial_algebra_ump_1_carrier_data_1.
      assert (f = idpath _) as p.
      { apply isapropunit. }    
      rewrite p.
      rewrite (functor_id (alg_constr_grpd H)). 
      exact group_quot_initial_algebra_ump_1_carrier_functor_id. 
    Qed.
    
    Definition group_quot_initial_algebra_ump_1_commute
      : functor_composite_data
          group_quot_initial_algebra_base_data
          group_quot_initial_algebra_ump_1_carrier_data
          ⟹
          functor_composite_data
          (poly_act_functor
             group_quot_point_constr
             group_quot_initial_algebra_ump_1_carrier)
          (alg_constr_grpd H).
    Proof.
      use make_nat_trans.
      - exact group_quot_initial_algebra_ump_1_commute_data.
      - exact group_quot_initial_algebra_ump_1_commute_is_nat_trans.
    Defined.

    Definition group_quot_initial_prealgebra_ump_1
      : pr11 group_quot_initial_algebra --> pr11 H.
    Proof.
      use make_hit_prealgebra_mor.
      - exact group_quot_initial_algebra_ump_1_carrier.
      - exact group_quot_initial_algebra_ump_1_commute.
    Defined.

    Definition group_quot_initial_algebra_ump_1
      : group_quot_initial_algebra --> H.
    Proof.
      use make_algebra_map_grpd.
      use make_hit_path_alg_map_grpd.
      - exact group_quot_initial_prealgebra_ump_1.
      - abstract
          (intros j x; 
           simpl;
           induction j;
           cbn;
           rewrite (functor_id (pr211 H));
           repeat rewrite (id_left _);
           exact (id_right _)).
    Defined.
  End GroupQuotInitialAlgUMPOne.

  Section GroupQuotInitialAlgUMPTwo.
    Variable (H : hit_algebra_grpd (group_quot_signature G))
             (F₁ F₂ : group_quot_initial_algebra --> H).

    Definition group_quot_initial_algebra_ump_2_carrier_data
      : nat_trans_data (pr111 (pr1 F₁)) (pr111 (pr1 F₂))
      := λ x, pr11 (pr211 F₁) x · grpd_inv (pr11 (pr211 F₂) x).

    Definition group_quot_initial_algebra_ump_2_is_nat_trans
      : is_nat_trans _ _ group_quot_initial_algebra_ump_2_carrier_data.
    Proof.
      intros x y.
      induction x, y.
      unfold group_quot_initial_algebra_ump_2_carrier_data.
      intro x.
      refine (assoc _ _ _ @ _).
      refine (!_) ; use move_grpd_inv_left.
      pose (m := pr21 F₁ tt).
      simpl in m.
      pose (nat_trans_eq_pointwise m x) as p.
      etrans.
      { 
        refine (! id_right _ @ _ @ assoc' _ _ _).
        apply maponpaths.
        exact (! functor_id (pr211 H) _).
      }
      refine (p @ _).
      refine (assoc' _ _ _ @ _ @ assoc _ _ _ @ assoc _ _ _).
      apply maponpaths.
      use move_grpd_inv_right.
      pose (m' := pr21 F₂ tt).
      simpl in m'.
      pose (nat_trans_eq_pointwise m' x) as p'.
      etrans.
      {
        refine (! id_right _ @ _ @ assoc' _ _ _).
        apply maponpaths.
        exact (! functor_id (pr211 H) _).
      }
      exact (p' @ assoc' _ _ _).
    Qed.
    
    Definition group_quot_initial_algebra_ump_2_carrier
      : pr111 (pr1 F₁) ⟹ pr111 (pr1 F₂).
    Proof.
      use make_nat_trans.
      - exact group_quot_initial_algebra_ump_2_carrier_data.
      - exact group_quot_initial_algebra_ump_2_is_nat_trans.
    Defined.

    Definition group_quot_initial_algebra_ump_2
      : F₁ ==> F₂.
    Proof.
      simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
      - exact group_quot_initial_algebra_ump_2_carrier.
      - abstract
          (use nat_trans_eq ;
           [ apply (pr1 (pr111 H))
           | simpl ;
             intro x ;
             unfold group_quot_initial_algebra_ump_2_carrier_data ;
             rewrite <- assoc ;
             apply maponpaths ;
             rewrite (functor_id (pr21 (pr1 H))) ;
             refine (!_) ;
             apply move_grpd_inv_right ;
             rewrite id_right ;
             apply idpath]).
    Defined.
  End GroupQuotInitialAlgUMPTwo.

  Section GroupQuotInitialAlgUMPEq.
    Variable (H : hit_algebra_grpd (group_quot_signature G))
             (F₁ F₂ : group_quot_initial_algebra --> H)
             (τ₁ τ₂ : F₁ ==> F₂).

    Definition group_quot_ump_eq
      : τ₁ = τ₂.
    Proof.
      use subtypePath.
      { intro ; apply isapropunit. }
      use subtypePath.
      { intro ; use impred ; intro ; apply isapropunit. }
      use subtypePath.
      { intro ; apply grpd_bicat. }
      use nat_trans_eq.
      { apply (pr1 (pr111 H)). }
      intro x ; induction x.
      pose (nat_trans_eq_pointwise (pr211 τ₁) tt) as p.
      pose (nat_trans_eq_pointwise (pr211 τ₂) tt) as q.
      cbn in p, q.
      rewrite (functor_id (pr21 (pr1 H))), id_right in p.
      rewrite (functor_id (pr21 (pr1 H))), id_right in q.
      pose (maponpaths (λ z, z · grpd_inv (pr11 (pr211 F₂) tt)) (p @ !q)) as r.
      simpl in r.
      refine (_ @ r @ _).
      - rewrite <- assoc.
        refine (!(id_right _) @ _).
        apply maponpaths.
        apply move_grpd_inv_left.
        rewrite id_left.
        apply idpath.
      - rewrite <- assoc.
        refine (!_).
        refine (!(id_right _) @ _).
        apply maponpaths.
        apply move_grpd_inv_left.
        rewrite id_left.
        apply idpath.
    Qed.
  End GroupQuotInitialAlgUMPEq.

  Definition group_quot_initial_algebra_unique_maps
    : is_biinitial group_quot_initial_algebra.
  Proof.
    use make_is_biinitial.
    - exact group_quot_initial_algebra_ump_1.
    - intros H f g.
      use make_invertible_2cell.
      + exact (group_quot_initial_algebra_ump_2 H f g).
      + apply hit_alg_is_invertible_2cell.
    - exact group_quot_ump_eq.
  Defined.    

  (** Path space of the group_quot at base *)
  Definition group_quot_path_space_base
    : UU
    := ((pr111 (initial_groupoid_algebra (group_quot_signature G)) : groupoid)
          ⟦ poly_initial_alg group_quot_point_constr tt
            , poly_initial_alg group_quot_point_constr tt ⟧).

  Definition group_quot_path_space_base_is_G
    : group_quot_path_space_base ≃ G.
  Proof.
    pose (left_adjoint_equivalence_grpd_algebra_is_fully_faithful
            (biinitial_unique_adj_eqv
               group_quot_initial_algebra_unique_maps
               (initial_groupoid_algebra_is_initial _))
            (poly_initial_alg group_quot_point_constr tt)
            (poly_initial_alg group_quot_point_constr tt))
      as f.
    exact (make_weq _ f).
  Defined.

  Definition group_quot_path_space_encode_decode
    : group_quot_base G (group_quot G) = group_quot_base G (group_quot G)
                                                         ≃
                                                         group_quot_path_space_base
    := hit_path_space
         (group_quot_signature G)
         (poly_initial_alg group_quot_point_constr tt)
         (poly_initial_alg group_quot_point_constr tt).
  
  Definition group_quot_path_space_is_G
    : group_quot_base G (group_quot G) = group_quot_base G (group_quot G) ≃ G
    := (group_quot_path_space_base_is_G ∘ group_quot_path_space_encode_decode)%weq.
End GroupQuotient.
