(**
Here we define the signature for the circle

The circle is the following HIT:
HIT circle :=
| base : circle
| loop : base = base
We look at the 1-truncation.
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
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

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

Local Open Scope cat.

Definition circle_point_constr
  : poly_code
  := C unit_one_type.

Inductive circle_paths : UU :=
| loop : circle_paths.

Definition circle_signature
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact circle_point_constr.
  - exact circle_paths.
  - exact (λ _, C unit_one_type).
  - exact (λ _, constr).
  - exact (λ _, constr).
  - exact empty.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
Defined.

(** Projections of circle algebra *)
Definition circle_base
           (X : hit_algebra_one_types circle_signature)
  : alg_carrier X
  := alg_constr X tt.

Definition circle_loop
           (X : hit_algebra_one_types circle_signature)
  : circle_base X = circle_base X
  := alg_path X loop tt.

Section CircleInduction.
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

Definition circle
  := pr1 (hit_existence circle_signature).


(*
Definition circle_path_space_base
  : UU
  := ((pr111 (initial_groupoid_algebra circle_signature) : groupoid)
        ⟦ poly_initial_alg circle_point_constr tt
        , poly_initial_alg circle_point_constr tt ⟧).

Definition circle_is_path_space
  : circle_base circle = circle_base circle
    ≃
    circle_path_space_base
  := hit_path_space
       circle_signature
       (poly_initial_alg circle_point_constr tt)
       (poly_initial_alg circle_point_constr tt).
 *)


(**
Initial groupoid algebra for the circle constructed in a special way.
We will use this conclude that the fundamental group of the circle is the integers
 *)
Definition TODO {A : UU} : A.
Admitted.

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
  use is_iso_qinv.
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

(** Induction for integers *)
Definition hz_ind
           {Y : hz → UU}
           (Yz : Y (0%hz))
           (Yplus : ∏ (n : nat), Y (nattohz n) → Y (nattohz (S n)))
           (Ymin : ∏ (n : nat), Y (toℤneg n) → Y (toℤneg (S n)))
           (z : hz)
  : Y z.
Proof.
  pose (hz_to_normal_form z) as znf.
  induction znf as [zpos | zneg].
  - induction zpos as [n p].
    refine (transportf Y p _).
    clear p z.
    induction n.
    + exact Yz.
    + exact (Yplus _ IHn).
  - induction zneg as [n p].
    refine (transportf Y p _).
    clear p z.
    induction n.
    + apply Ymin.
      apply Yz.
    + apply Ymin.
      exact IHn.
Defined.

(** The UMP for 1-cells *)
Section CircleInitialAlgUMPOne.
  Variable (G : hit_algebra_grpd circle_signature).

  Definition circle_initial_algebra_ump_1_carrier_data
    : functor_data
        circle_initial_algebra_precategory_data
        (alg_carrier_grpd G).
  Proof.
    use make_functor_data.
    - apply TODO.
    - apply TODO.
  Defined.

  Definition circle_initial_algebra_ump_1_carrier_is_functor
    : is_functor circle_initial_algebra_ump_1_carrier_data.
  Proof.
    split.
    - apply TODO.
    - apply TODO.
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
    apply TODO.
  Defined.

  Definition circle_initial_algebra_ump_1_commute_is_nat_trans
    : is_nat_trans
        _ _
        circle_initial_algebra_ump_1_commute_data.
  Proof.
    apply TODO.
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
    apply TODO.
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

Section CircleInitialAlgUMPTwo.
  Variable (G : hit_algebra_grpd circle_signature)
           (F₁ F₂ : circle_initial_algebra --> G).

  Definition circle_initial_algebra_ump_2_carrier_data
    : nat_trans_data (pr111 (pr1 F₁)) (pr111 (pr1 F₂))
    := λ x, pr11 (pr211 F₁) x · grpd_inv (pr11 (pr211 F₂) x).

  Definition circle_initial_algebra_ump_2_is_nat_trans
    : is_nat_trans _ _ circle_initial_algebra_ump_2_carrier_data.
  Proof.
    intros x y f.
    induction x, y.


    
    unfold circle_initial_algebra_ump_2_carrier_data.
    
    pose (nat_trans_eq_pointwise (pr21 F₁ loop) tt) as m.
    simpl in m.
    unfold circle_initial_algebra_loop_data in m.
    cbn in m.
    cbn in m.
    cbn in m.
    
    pose (pr212 (pr211 F₁)) as i.
    simpl in i.
    unfold is_nat_trans in i.
    simpl in i.

    pose (pr212 (pr11 F₁) _ _ (idpath tt)) as p.
    simpl in p.
    Opaque hz.
    simpl in f.
    pose (hz_to_normal_form  f).
    destruct h.
    - 
    simpl in h.
    rewrite (functor_id (pr211 G)) in p.
    rewrite id_right in p.


    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      unfold is_nat_trans in p.
      simpl in p.
      unfold 
    apply TODO.
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
