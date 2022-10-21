(**
We determine that the path space of the torus
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.NumberSystems.Integers.

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
Require Import examples.torus.

Require Import fundamental_groups.loops.

Local Open Scope cat.

(**
Initial groupoid algebra for the torus constructed in a special way.
We will use this conclude that the fundamental group of the circle is the integers
 *)
Definition torus_initial_algebra_precategory_data
  : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact unit. 
    + exact (λ _ _, hz × hz).
  - exact (λ _, hzzero ,, hzzero). 
  - exact (λ _ _ _ x y, (hzplus (pr1 x) (pr1 y) ,, hzplus (pr2 x) (pr2 y))).
Defined.

Definition torus_initial_algebra_is_precategory
  : is_precategory torus_initial_algebra_precategory_data.
Proof.
  use make_is_precategory.
  - intros ; apply pathsdirprod ; apply hzplusl0.
  - intros ; apply pathsdirprod ; apply hzplusr0.
  - intros ; apply pathsdirprod ; refine (!_) ; apply hzplusassoc.
  - intros ; apply pathsdirprod ; apply hzplusassoc.
Qed.

Definition torus_initial_algebra_precategory
  : precategory.
Proof.
  use make_precategory.
  - exact torus_initial_algebra_precategory_data.
  - exact torus_initial_algebra_is_precategory.
Defined.

Definition torus_initial_algebra_homsets
  : has_homsets torus_initial_algebra_precategory.
Proof.
  intros x y.
  apply isasetdirprod ; apply isasetsetquot.
Qed.

Definition torus_initial_algebra_category
  : category.
Proof.
  use make_category.
  - exact torus_initial_algebra_precategory.
  - exact torus_initial_algebra_homsets.
Defined.

Definition torus_initial_algebra_is_pregroupoid
  : is_pregroupoid torus_initial_algebra_category.
Proof.
  intros tt1 tt2 z.
  use make_is_z_isomorphism.
  - exact (hzsign (pr1 z) ,, hzsign (pr2 z)).
  - split.
    + apply pathsdirprod ; apply hzrminus.
    + apply pathsdirprod ; apply hzlminus.
Defined.

Definition torus_initial_algebra_carrier
  : groupoid.
Proof.
  use make_groupoid.
  - exact torus_initial_algebra_category.
  - exact torus_initial_algebra_is_pregroupoid.
Defined.

(** It forms a groupoid algebra *)
Definition torus_initial_algebra_base_data
  : functor_data
      (⦃ point_constr torus_signature ⦄ torus_initial_algebra_carrier : groupoid)
      (torus_initial_algebra_carrier).
Proof.
  use make_functor_data.
  - exact (λ x, x).
  - exact (λ _ _ _, hzzero ,, hzzero).
Defined.

Definition torus_initial_algebra_base_is_functor
  : is_functor torus_initial_algebra_base_data.
Proof.
  split.
  - exact (λ _, idpath _).
  - intro ; intros ; apply pathsdirprod ; refine (!_) ; apply hzplusr0.
Qed.

Definition torus_initial_algebra_base
  : (⦃ point_constr torus_signature ⦄ torus_initial_algebra_carrier : groupoid)
    ⟶
    torus_initial_algebra_carrier.
Proof.
  use make_functor.
  - exact torus_initial_algebra_base_data.
  - exact torus_initial_algebra_base_is_functor.
Defined.

Definition torus_initial_prealgebra
  : hit_prealgebra_grpd torus_signature.
Proof.
  use make_hit_prealgebra_grpd.
  - exact torus_initial_algebra_carrier.
  - exact torus_initial_algebra_base.
Defined.

Definition circle_initial_algebra_loop_l_data
  : nat_trans_data
      (sem_endpoint_grpd_data_functor_data constr torus_initial_prealgebra)
      (sem_endpoint_grpd_data_functor_data constr torus_initial_prealgebra)
  := λ _, hzone ,, hzzero.

Definition circle_initial_algebra_loop_l_is_nat_trans
  : is_nat_trans
      _ _
      circle_initial_algebra_loop_l_data.
Proof.
  intro ; intros.
  apply pathsdirprod ; refine (hzplusl0 _ @ !(hzplusr0 _)).
Qed.

Definition torus_initial_algebra_loop_l
  : sem_endpoint_grpd_data_functor_data constr torus_initial_prealgebra
    ⟹
    sem_endpoint_grpd_data_functor_data constr torus_initial_prealgebra.
Proof.
  use make_nat_trans.
  - exact circle_initial_algebra_loop_l_data.
  - exact circle_initial_algebra_loop_l_is_nat_trans.
Defined.

Definition circle_initial_algebra_loop_r_data
  : nat_trans_data
      (sem_endpoint_grpd_data_functor_data constr torus_initial_prealgebra)
      (sem_endpoint_grpd_data_functor_data constr torus_initial_prealgebra)
  := λ _, hzzero ,, hzone.

Definition circle_initial_algebra_loop_r_is_nat_trans
  : is_nat_trans
      _ _
      circle_initial_algebra_loop_r_data.
Proof.
  intro ; intros.
  apply pathsdirprod ; refine (hzplusl0 _ @ !(hzplusr0 _)).
Qed.

Definition torus_initial_algebra_loop_r
  : sem_endpoint_grpd_data_functor_data constr torus_initial_prealgebra
    ⟹
    sem_endpoint_grpd_data_functor_data constr torus_initial_prealgebra.
Proof.
  use make_nat_trans.
  - exact circle_initial_algebra_loop_r_data.
  - exact circle_initial_algebra_loop_r_is_nat_trans.
Defined.

Definition torus_initial_path_algebra
  : hit_path_algebra_grpd torus_signature.
Proof.
  use make_hit_path_algebra_grpd.
  - exact torus_initial_prealgebra.
  - intro j.
    induction j.
    + exact torus_initial_algebra_loop_l.
    + exact torus_initial_algebra_loop_r.
Defined.

Definition torus_initial_algebra
  : hit_algebra_grpd torus_signature.
Proof.
  use make_algebra_grpd.
  - exact torus_initial_path_algebra.
  - abstract (intros j z p ; apply idpath).
Defined.

(** The UMP for 1-cells *)
Local Notation "f ^ z" := (morph_power f z).

Section TorusInitialAlgUMPOne.
  Variable (G : hit_algebra_grpd torus_signature).

  Local Notation "'Gl'" := (pr1 (alg_path_grpd G p_left) tt).
  Local Notation "'Gr'" := (pr1 (alg_path_grpd G p_right) tt).

  Definition torus_initial_algebra_ump_1_carrier_data_0
    : alg_carrier_grpd G
    := alg_constr_grpd G tt.

  Definition torus_initial_algebra_ump_1_carrier_data_1
             (z : hz × hz)
    : alg_carrier_grpd G ⟦ torus_initial_algebra_ump_1_carrier_data_0 ,
                           torus_initial_algebra_ump_1_carrier_data_0 ⟧
    := double_power Gl Gr (pr1 z) (pr2 z).
  
  Definition torus_initial_algebra_ump_1_carrier_data
    : functor_data
        torus_initial_algebra_precategory_data
        (alg_carrier_grpd G).
  Proof.
    use make_functor_data.
    - exact (λ _, torus_initial_algebra_ump_1_carrier_data_0).
    - exact (λ _ _, torus_initial_algebra_ump_1_carrier_data_1). 
  Defined.

  Definition torus_initial_algebra_ump_1_carrier_is_functor
    : is_functor torus_initial_algebra_ump_1_carrier_data.
  Proof.
    split.
    - intro.
      simpl.
      cbn -[hz].
      apply id_right.
    - intros ? ? ?.
      cbn -[hz] ; unfold torus_initial_algebra_ump_1_carrier_data_1.
      intros f g.
      etrans.
      {
        apply maponpaths_2.
        exact (morph_power_plus Gl (pr1 f) (pr1 g)).
      }
      etrans.
      {
        apply maponpaths.
        exact (morph_power_plus Gr (pr2 f) (pr2 g)).
      }
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      apply maponpaths.
      refine (assoc _ _ _ @ _ @ assoc' _ _ _).
      apply maponpaths_2.
      refine (power_commute Gl Gr _ (pr1 g) (pr2 f)).
      exact (alg_homot_grpd G com tt (idpath _)).
  Qed.

  Definition torus_initial_algebra_ump_1_carrier
    : torus_initial_algebra_carrier ⟶ alg_carrier_grpd G.
  Proof.
    use make_functor.
    - exact torus_initial_algebra_ump_1_carrier_data.
    - exact torus_initial_algebra_ump_1_carrier_is_functor.
  Defined.

  Definition torus_initial_algebra_ump_1_commute_data
    : nat_trans_data
        (functor_composite_data
           torus_initial_algebra_base_data
           torus_initial_algebra_ump_1_carrier_data)
        (functor_composite_data
           (poly_act_functor
              torus_point_constr
              torus_initial_algebra_ump_1_carrier)
           (alg_constr_grpd G)).
  Proof.
    intros x.
    induction x ; simpl.
    apply id₁.
  Defined.

  Definition torus_initial_algebra_ump_1_commute_is_nat_trans
    : is_nat_trans
        _ _
        torus_initial_algebra_ump_1_commute_data.
  Proof.
    intros x y f.
    induction x, y.
    simpl.
    cbn.
    rewrite !id_left.
    assert (f = idpath _) as p.
    { apply isapropunit. }
    rewrite p.
    exact (!(functor_id (alg_constr_grpd G : _ ⟶ _) _)).
  Qed.
    
  Definition torus_initial_algebra_ump_1_commute
    : functor_composite_data
        torus_initial_algebra_base_data
        torus_initial_algebra_ump_1_carrier_data
      ⟹
      functor_composite_data
        (poly_act_functor
           torus_point_constr
           torus_initial_algebra_ump_1_carrier)
        (alg_constr_grpd G).
  Proof.
    use make_nat_trans.
    - exact torus_initial_algebra_ump_1_commute_data.
    - exact torus_initial_algebra_ump_1_commute_is_nat_trans.
  Defined.

  Definition torus_initial_prealgebra_ump_1
    : pr11 torus_initial_algebra --> pr11 G.
  Proof.
    use make_hit_prealgebra_mor.
    - exact torus_initial_algebra_ump_1_carrier.
    - exact torus_initial_algebra_ump_1_commute.
  Defined.

  Definition torus_initial_algebra_ump_1
    : torus_initial_algebra --> G.
  Proof.
    use make_algebra_map_grpd.
    use make_hit_path_alg_map_grpd.
    - exact torus_initial_prealgebra_ump_1.
    - abstract
        (intros j x ;
         simpl ;
         induction j, x ;
         [ cbn ;
           do  3 refine (id_right _ @ _) ;
           refine (!(id_left _)) 
         | cbn ;
           refine (id_right _ @ _) ;
           refine (id_left _ @ _) ;
           refine (id_right _ @ _) ;
           refine (!(id_left _))]).
  Defined.
End TorusInitialAlgUMPOne.

Local Notation "'loopl'" := (hzone ,, hzzero : torus_initial_algebra_carrier ⟦ tt , tt ⟧).
Local Notation "'loopr'" := (hzzero ,, hzone : torus_initial_algebra_carrier ⟦ tt , tt ⟧).

Definition loopl_power_n
           (n : hz)
  : loopl ^ n
    =
    (n ,, hzzero : torus_initial_algebra_carrier ⟦ tt , tt ⟧).
Proof.
  revert n.
  use hz_ind.
  - apply idpath.
  - simpl ; intros n IHn.
    rewrite nattohzandS.
    rewrite morph_power_plus.
    rewrite IHn.
    cbn ; apply idpath.
  - simpl ; intros n IHn.
    rewrite toℤneg_S.
    unfold hzminus.
    rewrite morph_power_plus.
    rewrite IHn.
    apply pathsdirprod.
    + simpl.
      rewrite !hzplusr0.
      apply idpath.
    + simpl.
      rewrite !hzplusr0.
      apply idpath.
Qed.

Definition loopr_power_n
           (n : hz)
  : loopr ^ n
    =
    (hzzero ,, n : torus_initial_algebra_carrier ⟦ tt , tt ⟧).
Proof.
  revert n.
  use hz_ind.
  - apply idpath.
  - simpl ; intros n IHn.
    rewrite nattohzandS.
    rewrite morph_power_plus.
    rewrite IHn.
    cbn ; apply idpath.
  - simpl ; intros n IHn.
    rewrite toℤneg_S.
    unfold hzminus.
    rewrite morph_power_plus.
    rewrite IHn.
    apply pathsdirprod.
    + simpl.
      rewrite !hzplusr0.
      apply idpath.
    + simpl.
      rewrite !hzplusr0.
      apply idpath.
Qed.
    
Definition is_double_power
           (f : torus_initial_algebra_carrier ⟦ tt , tt ⟧)
  : f
    =
    double_power
      loopl
      loopr
      (pr1 f)
      (pr2 f).
Proof.
  induction f as [n m].
  unfold double_power ; simpl.
  rewrite loopl_power_n.
  rewrite loopr_power_n.
  refine (!_).
  apply pathsdirprod.
  - apply hzplusr0.
  - apply hzplusl0.
Qed.

Definition torus_alg_mor_on_loop_l
           {G₁ G₂ : hit_algebra_grpd torus_signature}
           (F : G₁ --> G₂)
  : # (pr111 F : _ ⟶ _) (alg_path_grpd G₁ p_left tt) · (pr112 (pr11 F)) tt
    =
    (pr112 (pr11 F)) tt · alg_path_grpd G₂ p_left tt.
Proof.
  pose (pr21 F p_left) as m.
  simpl in m.
  pose (nat_trans_eq_pointwise m tt) as p.
  exact p.
Qed.

Definition torus_alg_mor_on_loop_r
           {G₁ G₂ : hit_algebra_grpd torus_signature}
           (F : G₁ --> G₂)
  : # (pr111 F : _ ⟶ _) (alg_path_grpd G₁ p_right tt) · (pr112 (pr11 F)) tt
    =
    (pr112 (pr11 F)) tt · alg_path_grpd G₂ p_right tt.
Proof.
  pose (pr21 F p_right) as m.
  simpl in m.
  pose (nat_trans_eq_pointwise m tt) as p.
  exact p.
Qed.

Section TorusInitialAlgUMPTwo.
  Variable (G : hit_algebra_grpd torus_signature)
           (F₁ F₂ : torus_initial_algebra --> G).

  Local Notation "'Gl'" := (pr1 (alg_path_grpd G p_left) tt).
  Local Notation "'Gr'" := (pr1 (alg_path_grpd G p_right) tt).
  
  Definition torus_initial_algebra_ump_2_carrier_data
    : nat_trans_data (pr111 (pr1 F₁)) (pr111 (pr1 F₂))
    := λ x, pr11 (pr211 F₁) x · grpd_inv (pr11 (pr211 F₂) x).

  Definition torus_initial_algebra_ump_2_is_nat_trans
    : is_nat_trans _ _ torus_initial_algebra_ump_2_carrier_data.
  Proof.
    intros x y.
    induction x, y.
    unfold torus_initial_algebra_ump_2_carrier_data.
    intro f.
    refine (assoc _ _ _ @ _).
    refine (!_) ; use move_grpd_inv_left.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (is_double_power f).
      }
      apply functor_on_double_power.
    }
    etrans.
    {
      apply (double_power_swap
               (torus_alg_mor_on_loop_l F₁)
               (torus_alg_mor_on_loop_r F₁)).
    }
    refine (assoc' _ _ _ @ _).
    do 2 refine (_ @ assoc _ _ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          exact (is_double_power f).
        }
        apply functor_on_double_power.
      }
      apply (double_power_swap
               (torus_alg_mor_on_loop_l F₂)
               (torus_alg_mor_on_loop_r F₂)).
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (assoc _ _ _ @ _).
    refine (_ @ id_left _).
    apply maponpaths_2.
    refine (!_).
    use move_grpd_inv_right.
    exact (!(id_right _)).
  Qed.
  
  Definition torus_initial_algebra_ump_2_carrier
    : pr111 (pr1 F₁) ⟹ pr111 (pr1 F₂).
  Proof.
    use make_nat_trans.
    - exact torus_initial_algebra_ump_2_carrier_data.
    - exact torus_initial_algebra_ump_2_is_nat_trans.
  Defined.

  Definition torus_initial_algebra_ump_2
    : F₁ ==> F₂.
  Proof.
    simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
    - exact torus_initial_algebra_ump_2_carrier.
    - abstract
        (use nat_trans_eq ;
         [ apply (pr1 (pr111 G))
         | simpl ;
           intro x ;
           unfold torus_initial_algebra_ump_2_carrier_data ;
           rewrite <- assoc ;
           apply maponpaths ;
           rewrite (functor_id (pr21 (pr1 G))) ;
           refine (!_) ;
           apply move_grpd_inv_right ;
           rewrite id_right ;
           apply idpath]).
  Defined.
End TorusInitialAlgUMPTwo.

Section TorusInitialAlgUMPEq.
  Variable (G : hit_algebra_grpd torus_signature)
           (F₁ F₂ : torus_initial_algebra --> G)
           (τ₁ τ₂ : F₁ ==> F₂).

  Definition torus_ump_eq
    : τ₁ = τ₂.
  Proof.
    use subtypePath.
    { intro ; apply isapropunit. }
    use subtypePath.
    { intro ; use impred ; intro ; apply isapropunit. }
    use subtypePath.
    { intro ; apply grpd_bicat. }
    use nat_trans_eq.
    { apply (pr1 (pr111 G)). }
    intro x ; induction x.
    pose (nat_trans_eq_pointwise (pr211 τ₁) tt) as p.
    pose (nat_trans_eq_pointwise (pr211 τ₂) tt) as q.
    cbn in p, q.
    rewrite (functor_id (pr21 (pr1 G))), id_right in p.
    rewrite (functor_id (pr21 (pr1 G))), id_right in q.
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
End TorusInitialAlgUMPEq.

Definition torus_initial_algebra_unique_maps
  : is_biinitial torus_initial_algebra.
Proof.
  use make_is_biinitial.
  - exact torus_initial_algebra_ump_1.
  - intros G f g.
    use make_invertible_2cell.
    + exact (torus_initial_algebra_ump_2 G f g).
    + apply hit_alg_is_invertible_2cell.
  - exact torus_ump_eq.
Defined.    

(** Path space of the circle at base *)
Definition torus_path_space_base
  : UU
  := ((pr111 (initial_groupoid_algebra torus_signature) : groupoid)
        ⟦ poly_initial_alg torus_point_constr tt
        , poly_initial_alg torus_point_constr tt ⟧).

Definition torus_path_space_base_is_ZZ
  : torus_path_space_base ≃ hz × hz.
Proof.
  pose (left_adjoint_equivalence_grpd_algebra_is_fully_faithful
          (biinitial_unique_adj_eqv
             torus_initial_algebra_unique_maps
             (initial_groupoid_algebra_is_initial _))
          (poly_initial_alg torus_point_constr tt)
          (poly_initial_alg torus_point_constr tt))
    as f.
  exact (make_weq _ f).
Defined.

Definition torus_path_space_encode_decode
  : torus_base torus = torus_base torus
    ≃
    torus_path_space_base
  := hit_path_space
       torus_signature
       (poly_initial_alg torus_point_constr tt)
       (poly_initial_alg torus_point_constr tt).

Definition torus_path_space_is_ZZ
  : torus_base torus = torus_base torus ≃ hz × hz
  := (torus_path_space_base_is_ZZ ∘ torus_path_space_encode_decode)%weq.
