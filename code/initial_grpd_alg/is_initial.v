(** Here we define the notion of a HIT *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.

Require Import initial_grpd_alg.W_poly.
Require Import initial_grpd_alg.initial_groupoid_algebra.

Local Open Scope cat.

Local Arguments nat_trans_comp {_ _ _ _ _} _ _.

Local Definition TODO {A : Type} : A.
Admitted.

Section ConstrUniqueMaps.
  Variable (B : bicat).
  
  Definition biinitial_1cell_property_help (X : B) : UU
    := ∏ (Y : B), X --> Y.

  Definition biinitial_2cell_property_help
             (X Y : B)
    : UU
    := ∏ (f g : X --> Y), invertible_2cell f g.

  Definition biinitial_eq_property_help (X Y : B) : UU
    := ∏ (f g : X --> Y) (α β : f ==> g), α = β.

  Definition make_unique_maps_help
             (X : B)
             (H₁ : biinitial_1cell_property_help X)
             (H₂ : ∏ (Y : B), biinitial_2cell_property_help X Y)
             (H₃ : ∏ (Y : B), biinitial_eq_property_help X Y)
             (Y : B)
    : equivalence_of_precats (hom X Y) unit_category.
  Proof.
    use tpair.
    - use tpair.
      + exact (functor_to_unit (hom X Y)).
      + use tpair.
        * use make_functor.
          ** use make_functor_data.
             *** exact (λ _, H₁ Y).
             *** exact (λ _ _ _, id₂ _).
          ** split.
             *** abstract
                   (intro ; simpl ;
                    apply idpath).
             *** abstract
                   (intros ? ? ? ? ? ; cbn ;
                    rewrite id2_left ;
                    apply idpath).
        * split.
          ** use make_nat_trans.
             *** intro x.
                 apply (H₂ Y).
             *** abstract
                   (intros x y f ; cbn ;
                    rewrite id2_right ;
                    apply H₃).
          ** use make_nat_trans.
             *** intro x.
                 apply isapropunit.
             *** abstract
                   (intros x y f ; cbn ;
                    apply isasetunit).
    - split.
      + intro ; simpl.
        apply inv2cell_to_iso.
      + intro ; simpl.
        apply path_univalent_groupoid.
  Defined.
  
  Definition make_unique_maps
             (X : B)
             (H₁ : biinitial_1cell_property_help X)
             (H₂ : ∏ (Y : B), biinitial_2cell_property_help X Y)
             (H₃ : ∏ (Y : B), biinitial_eq_property_help X Y)
    : unique_maps X.
  Proof.
    intro Y.
    refine (@adjointificiation
              (make_category (hom X Y) _)
              unit_category
              (make_unique_maps_help X H₁ H₂ H₃ Y)).
    intros ? ?.
    apply B.
  Defined.
End ConstrUniqueMaps.

Section GrpdAlgUMP.
  Variable (Σ : hit_signature).

  Section Univ1.
    Variable (Y : hit_algebra_grpd Σ).

    Definition univ1_functor_data_endpoint
               {P Q : poly_code}
               (e : endpoint (point_constr Σ) P Q)
               (x : poly_act P (poly_initial (point_constr Σ)))
      : poly_act_morphism
          Q
          (alg_carrier_grpd Y)
          (poly_map
             Q
             (poly_initial_rec
                (point_constr Σ)
                (alg_carrier_grpd Y)
                (pr121 (pr1 Y)))
             (sem_endpoint_UU e (poly_initial_alg (point_constr Σ)) x))
          (sem_endpoint_UU
             e
             (pr121 (pr1 Y))
             (poly_map
                P
                (poly_initial_rec
                   (point_constr Σ)
                   (alg_carrier_grpd Y)
                   (pr121 (pr1 Y)))
                x)).
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q
                      | P Q R e₁ IHe₁ e₂ IHe₂
                      | P T t | C₁ C₂ g | ].
      - (* Identity *)
        apply poly_act_identity.
      - (* Composition *)
        exact (poly_act_compose
                 (IHe₂ _)
                 (#(sem_endpoint_grpd_data_functor e₂ _) (IHe₁ x))).
      - (* Left inclusion *)
        apply poly_act_identity.
      - (* Right inclusion *)
        apply poly_act_identity.
      - (* Left projection *)
        apply poly_act_identity.
      - (* Right projection *)
        apply poly_act_identity.
      - (* Pairing *)
        exact (IHe₁ x ,, IHe₂ x).
      - (* Constant *)
        apply idpath.
      - (* Constant map *)
        apply idpath.
      - (* Constructor *)
        simpl.
        apply idtoiso.
        exact (poly_initial_comp
                 (point_constr Σ)
                 (alg_carrier_grpd Y)
                 (pr121 (pr1 Y))
                 x).
    Defined.

    Definition univ1_functor_data_help
               {P : poly_code}
               {x y : poly_act P (initial_groupoid_algebra_ob_poly (point_constr Σ))}
               (f : initial_groupoid_algebra_mor_el_poly
                      (path_left Σ)
                      (path_right Σ)
                      P
                      x y)
      : poly_act_morphism
          P
          (alg_carrier_grpd Y)
          (poly_map
             P
             (poly_initial_rec
                (point_constr Σ) (alg_carrier_grpd Y)
                (pr1 (pr211 Y)))
             x)
          (poly_map
             P
             (poly_initial_rec
                (point_constr Σ) (alg_carrier_grpd Y)
                (pr1 (pr211 Y)))
             y).
    Proof.
      induction f as [ P x | P x y f IHf | P x y z f₁ IHf₁ f₂ IHf₂
                       | j x | P Q x y f IHf | P Q x y f IHf
                       | P Q x₁ y₁ x₂ y₂ f₁ IHf₁ f₂ IHf₂
                       | x y f IHf ].
      - (* identity *)
        apply poly_act_identity.
      - (* inverse *)
        exact (poly_act_inverse IHf).
      - (* composition *)
        exact (poly_act_compose IHf₁ IHf₂).
      - (* path constructor *)
        simpl.
        refine (univ1_functor_data_endpoint
                  (path_left Σ j)
                  x
                · _).
        refine (pr1 (pr21 Y j)
                    (poly_map
                       (path_source Σ j)
                       (poly_initial_rec
                          (point_constr Σ)
                          (alg_carrier_grpd Y)
                          (pr121 (pr1 Y)))
                       x)
                · _) ; simpl.
        refine (inv_from_iso
                  (make_iso
                     (univ1_functor_data_endpoint (path_right Σ j) x)
                     _)).
        apply (alg_carrier_grpd Y).
      - (* inl *)
        exact IHf.
      - (* inr *)
        exact IHf.
      - (* pair *)
        exact (IHf₁ ,, IHf₂).
      - (* ap *)
        (* use computation rule of `poly_initial` *)
        refine (_ · (#(pr211 Y : _ ⟶ _) IHf) · _).
        + apply idtoiso.
          exact (poly_initial_comp
                   (point_constr Σ)
                   (alg_carrier_grpd Y)
                   (pr121 (pr1 Y))
                   x).
        + apply idtoiso.
          exact (!(poly_initial_comp
                     (point_constr Σ)
                     (alg_carrier_grpd Y)
                     (pr121 (pr1 Y))
                     y)).
    Defined.

    Definition univ1_functor_data_help_eq
               {P : poly_code}
               {x y : poly_act P (initial_groupoid_algebra_ob_poly (point_constr Σ))}
               {f₁ f₂ : initial_groupoid_algebra_mor_el_poly
                          (path_left Σ)
                          (path_right Σ)
                          P
                          x y}
               (r : initial_groupoid_algebra_mor_el_eq_UU f₁ f₂)
      : univ1_functor_data_help f₁ = univ1_functor_data_help f₂.
    Proof.
      induction r as [ P x y f | P x y f₁ f₂ r IHr
                       | P x y f₁ f₂ f₃ r₁ IHr₁ r₂ IHr₂
                       | x y f₁ f₂ r IHr | P x y f₁ f₂ r IHr
                       | P x y z f₁ f₂ g r IHr
                       | P x y z f g₁ g₂ r IHr
                       | P x y f | | | | ].
      - apply idpath.
      - exact (!IHr).
      - exact (IHr₁ @ IHr₂).
      - exact (maponpaths (λ z, (_ · # (pr211 Y : _ ⟶ _) z) · _) IHr).
      - exact (maponpaths poly_act_inverse IHr). 
      - exact (maponpaths (λ z, poly_act_compose z _) IHr).
      - exact (maponpaths (poly_act_compose _) IHr).
      - apply poly_act_id_right.
      - apply poly_act_id_left.
      - apply poly_act_assoc.
      - apply poly_act_inv_right.
      - apply poly_act_inv_left.
    Qed.

    Definition univ1_functor_data
      : functor_data
          (alg_carrier_grpd (initial_groupoid_algebra Σ))
          (alg_carrier_grpd Y).
    Proof.
      use make_functor_data.
      - apply poly_initial_rec.
        intro x.
        exact (pr1 (pr211 Y) x).
      - intros x y.
        simpl.
        use (setquotuniv
               (initial_groupoid_algebra_mor_el_eqrel Σ x y)
               (make_hSet _ _)).
        + apply homset_property.
        + exact univ1_functor_data_help.
        + intros f₁ f₂.
          use factor_through_squash.
          { apply homset_property. }
          exact univ1_functor_data_help_eq.
    Defined.

    Definition univ1_is_functor
      : is_functor univ1_functor_data.
    Proof.
      split.
      - intro x.
        apply idpath.
      - intros x y z.
        use (setquotunivprop _ (λ _, make_hProp _ _)).
        { use impred ; intro ; apply homset_property. }
        intro f.
        use (setquotunivprop _ (λ _, make_hProp _ _)).
        { apply homset_property. }
        intro g.
        apply idpath.
    Qed.
        
    Definition univ1_functor
      : alg_carrier_grpd (initial_groupoid_algebra Σ) ⟶ alg_carrier_grpd Y.
    Proof.
      use make_functor.
      - exact univ1_functor_data.
      - exact univ1_is_functor.
    Defined.

    Definition univ1_commute_data
      : nat_trans_data
          (initial_groupoid_algebra_point_constr Σ ∙ univ1_functor)
          (poly_act_functor (point_constr Σ) univ1_functor ∙ pr211 Y)
      := λ x,
         idtoiso
           (poly_initial_comp
              (point_constr Σ)
              (alg_carrier_grpd Y)
              (pr121 (pr1 Y))
              x).

    Definition univ1_is_nat_trans
      : is_nat_trans _ _ univ1_commute_data.
    Proof.
      intros x y f.
      simpl in f.
      cbn -[univ1_functor].
      assert (∏ g,
              # univ1_functor
                (initial_groupoid_algebra_point_constr_data_morph
                   Σ
                   g)
              · univ1_commute_data y
              =
              univ1_commute_data x
              · # (pr211 Y : _ ⟶ _)
                  (poly_act_functor_morphisms
                     (point_constr Σ)
                     univ1_functor
                     (quot_rel_poly_act _ g))).
      {
        clear f.
        use (setquotunivprop _ (λ _, make_hProp _ _)).
        - apply homset_property.
        - intro f.
          simpl.
          apply TODO.
      }
      refine (X _ @ _).
      do 3 apply maponpaths.
      apply TODO.
    Qed.

    Definition univ1_commute
      : initial_groupoid_algebra_point_constr Σ ∙ univ1_functor
        ⟹
        poly_act_functor (point_constr Σ) univ1_functor ∙ pr211 Y.
    Proof.
      use make_nat_trans.
      - exact univ1_commute_data.
      - exact univ1_is_nat_trans.
    Defined.
      
    Definition initial_groupoid_algebra_univ_1_eq
               (i : path_label Σ)
      : nat_trans_comp
          (post_whisker
             (initial_groupoid_algebra_path_constr Σ i)
             (poly_act_functor I univ1_functor))
          (sem_endpoint_grpd_natural
             (path_right Σ i)
             (univ1_functor
              ,,
              make_invertible_2cell (grpd_bicat_is_invertible_2cell univ1_commute)))
        =
        nat_trans_comp
          (sem_endpoint_grpd_natural
             (path_left Σ i)
             (univ1_functor
              ,,
              make_invertible_2cell (grpd_bicat_is_invertible_2cell univ1_commute)))
          (pre_whisker
             (poly_act_functor_data (path_source Σ i) univ1_functor)
             (pr21 Y i)).
    Proof.
      use nat_trans_eq.
      { apply homset_property. }
      intro x ; simpl in x.
      cbn.
      refine (!_).
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      refine (_ @ assoc _ _ _).
      refine (!(id_right _) @ _).
      apply maponpaths.
      refine (!_).
      apply iso_after_iso_inv.
    Qed.
  End Univ1.

  Definition initial_groupoid_algebra_univ_1
    : biinitial_1cell_property_help
        (hit_algebra_grpd Σ)
        (initial_groupoid_algebra Σ).
  Proof.
    intro Y.
    simple refine (((_ ,, _) ,, _) ,, tt).
    - exact (univ1_functor Y).
    - use make_invertible_2cell.
      + exact (univ1_commute Y).
      + apply grpd_bicat_is_invertible_2cell.
    - intro i.
      exact (initial_groupoid_algebra_univ_1_eq Y i).
  Defined.

  Section Univ2.
    Variable (Y : hit_algebra_grpd Σ)
             (f g : initial_groupoid_algebra Σ --> Y).

    Definition initial_groupoid_algebra_univ_2_nat_trans_data
      : nat_trans_data (pr111 (pr1 f)) (pr111 (pr1 g)).
    Proof.
      use W_ind_map ; simpl.
      intros i h H.
      pose (pr11 (pr211 f)
                 (interpret_poly
                    (point_constr Σ)
                    (poly_initial (point_constr Σ))
                    (i ,, h))) as m.
      cbn in m.
      refine (TODO · m · _).
      clear m.
      pose (pr11 (pr211 g)
                 (interpret_poly
                    (point_constr Σ)
                    (poly_initial (point_constr Σ))
                    (i ,, h))) as m.
      refine (_ · inv_from_iso (make_iso m TODO) · TODO).
      clear m ; simpl.
      refine (#(pr211 Y : _ ⟶ _) _).
      apply TODO.
    Defined.

    Definition initial_groupoid_algebra_univ_2_is_nat_trans
      : is_nat_trans _ _ initial_groupoid_algebra_univ_2_nat_trans_data.
    Proof.
      apply TODO.
    Qed.

    Definition initial_groupoid_algebra_univ_2_nat_trans
      : pr111 (pr1 f) ⟹ pr111 (pr1 g).
    Proof.
      use make_nat_trans.
      - exact initial_groupoid_algebra_univ_2_nat_trans_data.
      - exact initial_groupoid_algebra_univ_2_is_nat_trans.
    Defined.

    Definition initial_groupoid_algebra_univ_2_eq
               (z : poly_act (point_constr Σ) (initial_groupoid_algebra_ob Σ))
      : initial_groupoid_algebra_univ_2_nat_trans_data
          (poly_initial_alg (point_constr Σ) z)
        · (pr1 (pr211 g) : _ ⟹ _) z
        =
        (pr1 (pr211 f) : _ ⟹ _) z
        · # (pr121 (pr1 Y))
            (poly_act_nat_trans_data
               (point_constr Σ)
               initial_groupoid_algebra_univ_2_nat_trans
               z).
    Proof.
      simpl.
      apply TODO.
    Qed.
  End Univ2.

  Definition initial_groupoid_algebra_univ_2
             (Y : hit_algebra_grpd Σ)
    : biinitial_2cell_property_help (hit_algebra_grpd Σ) (initial_groupoid_algebra Σ) Y.
  Proof.
    intros f g.
    use make_invertible_2cell.
    - simple refine (((_ ,, _) ,, (λ _, tt)) ,, tt).
      + exact (initial_groupoid_algebra_univ_2_nat_trans Y f g).
      + abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           exact (initial_groupoid_algebra_univ_2_eq Y f g)).
    - apply hit_alg_is_invertible_2cell.
  Defined.

  Definition initial_groupoid_algebra_univ_eq
             (Y : hit_algebra_grpd Σ)
    : biinitial_eq_property_help (hit_algebra_grpd Σ) (initial_groupoid_algebra Σ) Y.
  Proof.
    intros f g p q.
    use subtypePath.
    { intro ; apply isapropunit. }
    use subtypePath.
    {
      intro.
      apply disp_2cells_isaprop_depprod ; intro.
      apply disp_2cells_isaprop_add_cell.
    }
    use subtypePath.
    {
      intro ; apply disp_2cells_isaprop_alg.
    }
    use nat_trans_eq.
    { apply homset_property. }
    use W_ind_map.
    cbn ; intros i h H.
    pose (nat_trans_eq_pointwise (pr211 p) (interpret_poly _ _ (i ,, h))) as h₁.
    pose (nat_trans_eq_pointwise (pr211 q) (interpret_poly _ _ (i ,, h))) as h₂.
    pose (cancel := pr11 (pr211 g)
                         (interpret_poly
                            (point_constr Σ)
                            (W (poly_container (point_constr Σ))) (i,, h))).
    unfold poly_initial_alg in h₁, h₂.
    refine (transportf
              (λ z,
               pr1 (pr111 p) (sup (poly_container (point_constr Σ)) z)
               =
               pr1 (pr111 q) (sup (poly_container (point_constr Σ)) z))
              (to_interpret_poly_interpret_poly (point_constr Σ) _ (i ,, h))
              _).
    apply (groupoid_cancel _ _ cancel).
    refine (h₁ @ _ @ !h₂).
    clear cancel h₁ h₂.
    refine (maponpaths (λ z, _ · # (pr121 (pr1 Y)) z) _).
    simpl.
    apply TODO.
    Time Qed.
    
  Definition initial_groupoid_algebra_is_initial
    : unique_maps (initial_groupoid_algebra Σ).
  Proof.
    use make_unique_maps.
    - exact initial_groupoid_algebra_univ_1.
    - exact initial_groupoid_algebra_univ_2.
    - exact initial_groupoid_algebra_univ_eq.
  Defined.
End GrpdAlgUMP.
