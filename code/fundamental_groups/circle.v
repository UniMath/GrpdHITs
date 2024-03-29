(**
We show that the path space of the circle is the integers
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
Require Import examples.circle.

Require Import fundamental_groups.loops.

Local Open Scope cat.
Local Open Scope hz.

(**
Initial groupoid algebra for the circle constructed in a special way.
We will use this conclude that the fundamental group of the circle is the integers
 *)
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
  use make_is_z_isomorphism.
  - exact (hzsign z).
  - split.
    + exact (hzrminus z).
    + exact (hzlminus z).
Defined.

Definition circle_initial_algebra_carrier
  : groupoid.
Proof.
  use make_groupoid.
  - exact circle_initial_algebra_category.
  - exact circle_initial_algebra_is_pregroupoid.
Defined.

(** It forms a groupoid algebra *)
Definition circle_initial_algebra_base_data
  : functor_data
      (⦃ point_constr circle_signature ⦄ circle_initial_algebra_carrier : groupoid)
      (circle_initial_algebra_carrier).
Proof.
  use make_functor_data.
  - exact (λ x, x).
  - exact (λ _ _ _, hzzero).
Defined.

Definition circle_initial_algebra_base_is_functor
  : is_functor circle_initial_algebra_base_data.
Proof.
  split.
  - exact (λ _, idpath _).
  - exact (λ _ _ _ _ _, ! hzplusr0 _).
Qed.

Definition circle_initial_algebra_base
  : (⦃ point_constr circle_signature ⦄ circle_initial_algebra_carrier : groupoid)
    ⟶
    circle_initial_algebra_carrier.
Proof.
  use make_functor.
  - exact circle_initial_algebra_base_data.
  - exact circle_initial_algebra_base_is_functor.
Defined.

Definition circle_initial_prealgebra
  : hit_prealgebra_grpd circle_signature.
Proof.
  use make_hit_prealgebra_grpd.
  - exact circle_initial_algebra_carrier.
  - exact circle_initial_algebra_base.
Defined.

Definition circle_initial_algebra_loop_data
  : nat_trans_data
      (sem_endpoint_grpd_data_functor_data constr circle_initial_prealgebra)
      (sem_endpoint_grpd_data_functor_data constr circle_initial_prealgebra)
  := λ _, hzone.

Definition circle_initial_algebra_loop_is_nat_trans
  : is_nat_trans
      _ _
      circle_initial_algebra_loop_data.
Proof.
  exact (λ _ _ _, hzplusl0 _ @ ! hzplusr0 _).
Qed.

Definition circle_initial_algebra_loop
  : sem_endpoint_grpd_data_functor_data constr circle_initial_prealgebra
    ⟹
    sem_endpoint_grpd_data_functor_data constr circle_initial_prealgebra.
Proof.
  use make_nat_trans.
  - exact circle_initial_algebra_loop_data.
  - exact circle_initial_algebra_loop_is_nat_trans.
Defined.
  
Definition circle_initial_path_algebra
  : hit_path_algebra_grpd circle_signature.
Proof.
  use make_hit_path_algebra_grpd.
  - exact circle_initial_prealgebra.
  - exact (λ _, circle_initial_algebra_loop).
Defined.

Definition circle_initial_algebra
  : hit_algebra_grpd circle_signature.
Proof.
  use make_algebra_grpd.
  - exact circle_initial_path_algebra.
  - abstract (intro j ; induction j).
Defined.

(** The UMP for 1-cells *)
Local Notation "f ^ z" := (morph_power f z).

Section CircleInitialAlgUMPOne.
  Variable (G : hit_algebra_grpd circle_signature).

  Local Notation "'Gloop'" := (pr1 (alg_path_grpd G loop) tt).

  Definition circle_initial_algebra_ump_1_carrier_data_0
    : alg_carrier_grpd G
    := alg_constr_grpd G tt.

  Definition circle_initial_algebra_ump_1_carrier_data_1
             (z : hz)
    : alg_carrier_grpd G ⟦ circle_initial_algebra_ump_1_carrier_data_0 ,
                           circle_initial_algebra_ump_1_carrier_data_0 ⟧
    := Gloop ^ z.
  
  Definition circle_initial_algebra_ump_1_carrier_data
    : functor_data
        circle_initial_algebra_precategory_data
        (alg_carrier_grpd G).
  Proof.
    use make_functor_data.
    - exact (λ _, circle_initial_algebra_ump_1_carrier_data_0).
    - exact (λ _ _, circle_initial_algebra_ump_1_carrier_data_1). 
  Defined.

  Definition circle_initial_algebra_ump_1_carrier_is_functor
    : is_functor circle_initial_algebra_ump_1_carrier_data.
  Proof.
    split.
    - exact (λ _, idpath _).
    - intros ? ? ?.
      cbn -[hz] ; unfold circle_initial_algebra_ump_1_carrier_data_1.
      intros f g.
      exact (morph_power_plus Gloop f g).
  Qed.

  Definition circle_initial_algebra_ump_1_carrier
    : circle_initial_algebra_carrier ⟶ alg_carrier_grpd G.
  Proof.
    use make_functor.
    - exact circle_initial_algebra_ump_1_carrier_data.
    - exact circle_initial_algebra_ump_1_carrier_is_functor.
  Defined.

  Definition circle_initial_algebra_ump_1_commute_data
    : nat_trans_data
        (functor_composite_data
           circle_initial_algebra_base_data
           circle_initial_algebra_ump_1_carrier_data)
        (functor_composite_data
           (poly_act_functor
              circle_point_constr
              circle_initial_algebra_ump_1_carrier)
           (alg_constr_grpd G)).
  Proof.
    intros x.
    induction x ; simpl.
    apply id₁.
  Defined.

  Definition circle_initial_algebra_ump_1_commute_is_nat_trans
    : is_nat_trans
        _ _
        circle_initial_algebra_ump_1_commute_data.
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
    
  Definition circle_initial_algebra_ump_1_commute
    : functor_composite_data
        circle_initial_algebra_base_data
        circle_initial_algebra_ump_1_carrier_data
      ⟹
      functor_composite_data
        (poly_act_functor
           circle_point_constr
           circle_initial_algebra_ump_1_carrier)
        (alg_constr_grpd G).
  Proof.
    use make_nat_trans.
    - exact circle_initial_algebra_ump_1_commute_data.
    - exact circle_initial_algebra_ump_1_commute_is_nat_trans.
  Defined.

  Definition circle_initial_prealgebra_ump_1
    : pr11 circle_initial_algebra --> pr11 G.
  Proof.
    use make_hit_prealgebra_mor.
    - exact circle_initial_algebra_ump_1_carrier.
    - exact circle_initial_algebra_ump_1_commute.
  Defined.

  (** Might need to change once the definitions can be unfolded more *)
  Definition circle_initial_algebra_ump_1_path
             (j : path_label circle_signature)
             (x : unit)
    : # (pr11 circle_initial_prealgebra_ump_1)
        (circle_initial_algebra_loop_data x)
      · (pr112 circle_initial_prealgebra_ump_1) x
      =
      (pr112 circle_initial_prealgebra_ump_1) x · pr1 ((pr21 G) j) x.
  Proof.
    cbn.
    induction x, j.
    cbn.
    rewrite !id_right, id_left.
    apply idpath.
  Qed.
  
  Definition circle_initial_algebra_ump_1
    : circle_initial_algebra --> G.
  Proof.
    use make_algebra_map_grpd.
    use make_hit_path_alg_map_grpd.
    - exact circle_initial_prealgebra_ump_1.
    - exact circle_initial_algebra_ump_1_path.
  Defined.
End CircleInitialAlgUMPOne.

Definition morph_is_a_power_morph
           (f : circle_initial_algebra_carrier ⟦ tt , tt ⟧)
  : f = (hzone : circle_initial_algebra_carrier ⟦ _ , _ ⟧) ^ f.
Proof.
  revert f.
  use hz_ind.
  - cbn ; apply idpath.
  - simpl.
    intros n IHn.
    rewrite !nattohzandS.
    etrans.
    {
      apply maponpaths.
      exact IHn.
    }
    rewrite morph_power_plus.
    apply maponpaths_2.
    cbn ; apply idpath.
  - simpl.
    intros n IHn.
    rewrite !toℤneg_S.
    etrans.
    {
      apply maponpaths_2.
      exact IHn.
    }
    unfold hzminus.
    rewrite morph_power_plus.
    refine (maponpaths (λ z, z + _) _).
    apply idpath.
Qed.

Definition circle_alg_mor_on_loop
           {G₁ G₂ : hit_algebra_grpd circle_signature}
           (F : G₁ --> G₂)
  : # (pr111 F : _ ⟶ _) (alg_path_grpd G₁ loop tt) · (pr112 (pr11 F)) tt
    =
    (pr112 (pr11 F)) tt · alg_path_grpd G₂ loop tt.
Proof.
  pose (pr21 F loop) as m.
  simpl in m.
  pose (nat_trans_eq_pointwise m tt) as p.
  exact p.
Qed.

Section CircleInitialAlgUMPTwo.
  Variable (G : hit_algebra_grpd circle_signature)
           (F₁ F₂ : circle_initial_algebra --> G).

  Definition circle_initial_algebra_ump_2_carrier_data
    : nat_trans_data (pr111 (pr1 F₁)) (pr111 (pr1 F₂))
    := λ x, pr11 (pr211 F₁) x · grpd_inv (pr11 (pr211 F₂) x).

  Definition circle_initial_algebra_ump_2_is_nat_trans
    : is_nat_trans _ _ circle_initial_algebra_ump_2_carrier_data.
  Proof.
    intros x y.
    induction x, y.
    unfold circle_initial_algebra_ump_2_carrier_data.
    intro f.
    refine (assoc _ _ _ @ _).
    refine (!_) ; use move_grpd_inv_left.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (morph_is_a_power_morph f).
      }
      apply functor_on_morpower.
    }
    etrans.
    {
      exact (power_swap (circle_alg_mor_on_loop F₁) f).
    }
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
          exact (morph_is_a_power_morph f).
        }
        apply functor_on_morpower.
      }
      exact (power_swap (circle_alg_mor_on_loop F₂) f).
    }
    refine (assoc _ _ _ @ _ @ id_left _).
    apply maponpaths_2.
    refine (!_).
    use move_grpd_inv_right.
    exact (!(id_right _)).
  Qed.
  
  Definition circle_initial_algebra_ump_2_carrier
    : pr111 (pr1 F₁) ⟹ pr111 (pr1 F₂).
  Proof.
    use make_nat_trans.
    - exact circle_initial_algebra_ump_2_carrier_data.
    - exact circle_initial_algebra_ump_2_is_nat_trans.
  Defined.

  Definition circle_initial_algebra_ump_2
    : F₁ ==> F₂.
  Proof.
    simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
    - exact circle_initial_algebra_ump_2_carrier.
    - abstract
        (use nat_trans_eq ;
         [ apply (pr1 (pr111 G))
         | simpl ;
           intro x ;
           unfold circle_initial_algebra_ump_2_carrier_data ;
           rewrite <- assoc ;
           apply maponpaths ;
           rewrite (functor_id (pr21 (pr1 G))) ;
           refine (!_) ;
           apply move_grpd_inv_right ;
           rewrite id_right ;
           apply idpath]).
  Defined.
End CircleInitialAlgUMPTwo.

Section CircleInitialAlgUMPEq.
  Variable (G : hit_algebra_grpd circle_signature)
           (F₁ F₂ : circle_initial_algebra --> G)
           (τ₁ τ₂ : F₁ ==> F₂).

  Definition circle_ump_eq
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
End CircleInitialAlgUMPEq.

Definition circle_initial_algebra_unique_maps
  : is_biinitial circle_initial_algebra.
Proof.
  use make_is_biinitial.
  - exact circle_initial_algebra_ump_1.
  - intros G f g.
    use make_invertible_2cell.
    + exact (circle_initial_algebra_ump_2 G f g).
    + apply hit_alg_is_invertible_2cell.
  - exact circle_ump_eq.
Defined.    

(** Path space of the circle at base *)
Definition circle_path_space_base
  : UU
  := ((pr111 (initial_groupoid_algebra circle_signature) : groupoid)
        ⟦ poly_initial_alg circle_point_constr tt
        , poly_initial_alg circle_point_constr tt ⟧).

Definition circle_path_space_base_is_Z
  : circle_path_space_base ≃ hz.
Proof.
  pose (left_adjoint_equivalence_grpd_algebra_is_fully_faithful
          (biinitial_unique_adj_eqv
             circle_initial_algebra_unique_maps
             (initial_groupoid_algebra_is_initial _))
          (poly_initial_alg circle_point_constr tt)
          (poly_initial_alg circle_point_constr tt))
    as f.
  exact (make_weq _ f).
Defined.

Definition circle_path_space_encode_decode
  : circle_base circle = circle_base circle
    ≃
    circle_path_space_base
  := hit_path_space
       circle_signature
       (poly_initial_alg circle_point_constr tt)
       (poly_initial_alg circle_point_constr tt).

Definition circle_path_space_is_Z
  : circle_base circle = circle_base circle ≃ hz
  := (circle_path_space_base_is_Z ∘ circle_path_space_encode_decode)%weq.
