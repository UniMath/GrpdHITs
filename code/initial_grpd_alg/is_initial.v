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
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.
Require Import algebra.one_types_polynomials.
Require Import displayed_algebras.displayed_algebra.

Require Import initial_grpd_alg.W_poly.
Require Import initial_grpd_alg.relation_2.
Require Import initial_grpd_alg.initial_groupoid_algebra.

Local Open Scope cat.

Local Arguments nat_trans_comp {_ _ _ _ _} _ _.

(** MOVE TO GROUPOID_HOMOTOPIES *)
Definition grpd_map_path_rule
           {Σ : hit_signature}
           {X₁ X₂ : hit_algebra_grpd Σ}
           (h : X₁ --> X₂)
           (j : path_label Σ)
  : nat_trans_comp
      (post_whisker
         (pr21 X₁ j)
         (poly_act_functor I (pr111 h)))
      (sem_endpoint_grpd_natural (path_right Σ j) (pr11 h))
    =
    nat_trans_comp
      (sem_endpoint_grpd_natural
         (path_left Σ j)
         (pr11 h))
      (pre_whisker
         (poly_act_functor_data (path_source Σ j) (pr111 h))
         (pr21 X₂ j))
  := pr21 h j.

Definition grpd_map_path_rule_pointwise
           {Σ : hit_signature}
           {X₁ X₂ : hit_algebra_grpd Σ}
           (h : X₁ --> X₂)
           (j : path_label Σ)
           (x : poly_act (path_source Σ j) (pr111 (pr1 X₁)))
  := nat_trans_eq_pointwise (grpd_map_path_rule h j) x.




Definition poly_act_inverse_compose
           {P : poly_code}
           {G : groupoid}
           {x y z : poly_act P G}
           (f : poly_act_morphism P G x y)
           (g : poly_act_morphism P G y z)
  : poly_act_inverse
      (poly_act_compose f g)
    =
    poly_act_compose
      (poly_act_inverse g)
      (poly_act_inverse f).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply pathscomp_inv.
  - simpl.
    use iso_inv_on_left.
    simpl.
    refine (!_).
    use iso_inv_on_right.
    simpl.
    refine (!_).
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      exact (iso_inv_after_iso (make_iso g _)).
    }
    apply id_right.
  - induction x as [x | x], y as [y | y], z as [z | z]
    ; try induction f ; try induction g.
    + apply IHP₁.
    + apply IHP₂.
  - exact (pathsdirprod (IHP₁ _ _ _ _ _) (IHP₂ _ _ _ _ _)).
Qed.

Definition poly_act_inverse_inverse
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (f : poly_act_morphism P G x y)
  : poly_act_inverse (poly_act_inverse f)
    =
    f.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply pathsinv0inv0.
  - simpl.
    refine (!_).
    use inv_iso_unique'.
    apply iso_after_iso_inv.
  - induction x as [x | x], y as [y | y]
    ; try induction f.
    + apply IHP₁.
    + apply IHP₂.
  - exact (pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _)).  
Qed.

Definition grpd_inv
           {G : groupoid}
           {x y : G}
           (f : x --> y)
  : y --> x
  := inv_from_iso (make_iso f (pr2 G _ _ f)).

Definition poly_act_inverse_functor
           {P : poly_code}
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ poly_act_groupoid P G₂)
           {x y : G₁}
           (m : x --> y)
  : poly_act_inverse (# F m)
    =
    # F (grpd_inv m).
Proof.
  refine (!_).
  etrans.
  {
    refine (!_).
    exact (functor_on_inv_from_iso' F (pr2 G₁ _ _ m)).
  }
  refine (!_).
  use inv_iso_unique'.
  apply poly_act_inv_right.
Qed.

Definition poly_act_inverse_identity
           {P : poly_code}
           {G : groupoid}
           (x : poly_act P G)
  : poly_act_inverse (poly_act_identity x)
    =
    poly_act_identity x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - refine (!_).
    use inv_iso_unique'.
    apply id_left.
  - induction x as [x | x].
    + apply IHP₁.
    + apply IHP₂.
  - exact (pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition is_grpd_inv
           {G : groupoid}
           {x y : G}
           {f : x --> y}
           {g :  y --> x}
  : f · g = identity _ → g = grpd_inv f.
Proof.
  intro p.
  use inv_iso_unique'.
  exact p.
Qed.

Definition move_grpd_inv_left
           {G : groupoid}
           {x y z : G}
           {f : x --> y} {g : y --> z} {h : x --> z}
  : h = f · g → f = h · grpd_inv g.
Proof.
  intro p.  
  apply iso_inv_on_left.
  exact p.
Qed.

Definition move_grpd_inv_right
           {G : groupoid}
           {x y z : G}
           {f : x --> y} {g : y --> z} {h : x --> z}
  : h = f · g → g = grpd_inv f · h.
Proof.
  intro p.
  refine (!_).
  apply iso_inv_on_right.
  exact p.
Qed.

Definition grpd_inv_nat_trans_ax
           {G₁ G₂ : groupoid}
           {F₁ F₂ : G₁ ⟶ G₂}
           (n : F₁ ⟹ F₂)
           {x y : G₁}
           (f : x --> y)
  : grpd_inv (n x) · # F₁ f = # F₂ f · grpd_inv (n y).
Proof.
  refine (!_).
  use move_grpd_inv_right.
  refine (_ @ assoc' _ _ _).
  use move_grpd_inv_left.
  refine (!_).
  apply nat_trans_ax.
Qed.

Definition poly_act_rel_map
           {P : poly_code}
           {X Y : UU}
           (f : X → Y)
           {RX : X → X → UU}
           {RY : Y → Y → UU}
           (f_resp : ∏ (x₁ x₂ : X), RX x₁ x₂ → RY (f x₁) (f x₂))
           {x y : poly_act P X}
           (z : poly_act_rel P RX x y)
  : poly_act_rel P RY (poly_map P f x) (poly_map P f y).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact z.
  - exact (f_resp _ _ z).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y z).
    + exact (fromempty z).
    + exact (fromempty z).
    + exact (IHP₂ x y z).
  - exact (IHP₁ _ _ (pr1 z) ,, IHP₂ _ _ (pr2 z)).
Defined.

Definition initial_groupoid_algebra_univ_2_nat_trans_data_help
           {P : poly_code}
           {X : UU}
           {G : groupoid}
           {f g : X → G}
           {x : poly_act P X}
           (H : poly_dact_UU P (λ x, f x --> g x) x)
  : poly_act_morphism
      P G
      (poly_map P f x)
      (poly_map P g x).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply H.
  - induction x as [x | x].
    + exact (IHP₁ x H).
    + exact (IHP₂ x H).
  - exact (IHP₁ _ (pr1 H) ,, IHP₂ _ (pr2 H)).
Defined.

Definition initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap
           {P : poly_code}
           {X : UU}
           {G : groupoid}
           {f g : X → G}
           {x : poly_act P X}
           (m : ∏ (x : X), f x --> g x)
  : initial_groupoid_algebra_univ_2_nat_trans_data_help
      (poly_dmap
         P
         (λ x, f x --> g x)
         m
         x)
    =
    poly_act_nat_trans_data_help P m x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition initial_groupoid_algebra_univ_eq_help
           (P : poly_code)
           {X : UU}
           {G : groupoid}
           {f g : X → G}
           {p q : ∏ (x : X), f x --> g x}
           {x : poly_act P X}
           (Hx : poly_dact_UU P (λ x, p x = q x) x)
  : poly_act_nat_trans_data_help P p x
    =
    poly_act_nat_trans_data_help P q x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply Hx.
  - induction x as [x | x].
    + exact (IHP₁ x Hx).
    + exact (IHP₂ x Hx).
  - exact (pathsdirprod (IHP₁ _ (pr1 Hx)) (IHP₂ _ (pr2 Hx))).
Defined.

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

    Definition poly_initial_comp_mor
               (x : poly_act
                      (point_constr Σ)
                      (initial_groupoid_algebra_ob_poly (point_constr Σ)))
      : (pr111 Y : groupoid)
        ⟦ poly_initial_rec
            (point_constr Σ)
            (alg_carrier_grpd Y)
            (pr121 (pr1 Y))
            (poly_initial_alg (point_constr Σ) x),
          (pr211 Y : _ ⟶ _)
            (poly_map
               (point_constr Σ)
               (poly_initial_rec
                  (point_constr Σ)
                  (alg_carrier_grpd Y)
                  (pr121 (pr1 Y)))
               x) ⟧.
    Proof.
      apply idtoiso.
      exact (poly_initial_comp
               (point_constr Σ)
               (alg_carrier_grpd Y)
               (pr121 (pr1 Y))
               x).
    Defined.

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
        exact (poly_initial_comp_mor x).
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
        refine (_ · (#(pr211 Y : _ ⟶ _) IHf) · _) ; clear IHf.
        + exact (poly_initial_comp_mor x).
        + refine (inv_from_iso (make_iso (poly_initial_comp_mor y) _)).
          apply idtoiso.
    Defined.

    Definition univ1_functor_data_help_eq_id
               {P : poly_code}
               (x : poly_act P (initial_groupoid_algebra_ob Σ))
      :  univ1_functor_data_help
           (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
              (poly_act_rel_identity
                 P
                 (initial_groupoid_algebra_mor_el_poly
                    (path_left Σ) (path_right Σ) I)
                 initial_alg_id
                 x))
         =
         poly_act_identity
           (poly_map
              P
              (poly_initial_rec (point_constr Σ) (alg_carrier_grpd Y) (pr121 (pr1 Y))) x).
    Proof.
      induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
      - apply idpath.
      - apply idpath.
      - induction x as [x | x].
        + apply IHP₁.
        + apply IHP₂.
      - exact (pathsdirprod (IHP₁ _) (IHP₂ _)).
    Qed.
    
    Definition univ1_functor_data_help_eq_inv
               {P : poly_code}
               {x y : poly_act
                        P
                        (initial_groupoid_algebra_ob_poly (point_constr Σ))}
               (f : poly_act_rel
                      P
                      (initial_groupoid_algebra_mor_el_poly
                         (path_left Σ)
                         (path_right Σ)
                         I)
                      x y)
      : univ1_functor_data_help
          (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
             (poly_act_rel_inv
                P
                _
                (@initial_alg_inv
                   (point_constr Σ) (path_label Σ) (path_source Σ) 
                   (path_left Σ) (path_right Σ) I)
                (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel
                   (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
                      f))))
        =
        poly_act_inverse
          (univ1_functor_data_help
             (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
                f)).
    Proof.
      induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
      - induction f.
        apply idpath.
      - simpl.
        apply maponpaths.
        use subtypePath.
        { intro ; apply isaprop_is_iso. }
        simpl.
        apply maponpaths.
        exact (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec f).
      - induction x as [x | x], y as [y | y].
        + apply IHP₁.
        + induction f.
        + induction f.          
        + apply IHP₂.
      - exact (pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _)).
    Qed.

    Definition univ1_functor_data_help_eq_comp
               {P : poly_code}
               {x y z : poly_act
                        P
                        (initial_groupoid_algebra_ob_poly (point_constr Σ))}
               (f : poly_act_rel
                      P
                      (initial_groupoid_algebra_mor_el_poly
                         (path_left Σ)
                         (path_right Σ)
                         I)
                      x y)
               (g : poly_act_rel
                      P
                      (initial_groupoid_algebra_mor_el_poly
                         (path_left Σ)
                         (path_right Σ)
                         I)
                      y z)
      : univ1_functor_data_help
          (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
             (poly_act_rel_comp
                P
                _
                (@initial_alg_comp
                   (point_constr Σ) (path_label Σ) (path_source Σ) 
                   (path_left Σ) (path_right Σ) I)
                (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel
                   (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
                      f))
                (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel
                   (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
                      g))))
        =
        poly_act_compose
          (univ1_functor_data_help
             (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
                f))
          (univ1_functor_data_help
             (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
                g)).
    Proof.
      induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
      - induction f, g.
        apply idpath.
      - simpl.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec f).
        }
        do 2 apply maponpaths.
        exact (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec g).
      - induction x as [x | x], y as [y | y], z as [z | z]
        ; try induction f ; try induction g.
        + apply IHP₁.
        + apply IHP₂.
      - exact (pathsdirprod (IHP₁ _ _ _ _ _) (IHP₂ _ _ _ _ _)).
    Qed.

    Definition univ1_functor_data_help_eq_constr
               (P : poly_code)
               {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
               (p : poly_act_rel P initial_groupoid_algebra_mor_el x y)
      : univ1_functor_data_help
          (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly p)
        =
        poly_act_rel_map
          (poly_initial_rec (point_constr Σ) (alg_carrier_grpd Y) (pr121 (pr1 Y)))
          (λ _ _ g,
           univ1_functor_data_help g)
          p.
    Proof.
      induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
      - induction p.
        apply idpath.
      - apply idpath.
      - induction x as [x | x], y as [y | y].
        + apply IHP₁.
        + induction p.
        + induction p.
        + apply IHP₂.
      - exact (pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _)).
    Qed.

    Definition univ1_functor_data_help_eq_natural
               {P Q : poly_code}
               (e : endpoint (point_constr Σ) P Q)
               {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
               (p : poly_act_rel P initial_groupoid_algebra_mor_el x y)
      : poly_act_compose
           (poly_act_rel_map
              _
              (λ _ _ g, univ1_functor_data_help g)
              (sem_endpoint_initial_terms e p))
           (univ1_functor_data_endpoint e y)
         =
         poly_act_compose
           (univ1_functor_data_endpoint e x)
           (sem_endpoint_grpd_data_functor_morphism
              e
              (pr211 Y)
              (poly_act_rel_map
                 (poly_map
                    I
                    (poly_initial_rec
                       (point_constr Σ)
                       (alg_carrier_grpd Y)
                       (pr121 (pr1 Y))))
                 (λ _ _ g, univ1_functor_data_help g)
                 p)).
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q
                      | P Q R e₁ IHe₁ e₂ IHe₂
                      | P T t | C₁ C₂ g | ].
      - (* Identity *)
        exact (poly_act_id_right _ @ !(poly_act_id_left _)).
      - (* Composition *)
        simpl.
        etrans.
        {
          apply poly_act_assoc.
        }
        etrans.
        {
          apply maponpaths_2.
          apply IHe₂.
        }
        etrans.
        {
          refine (!_).
          apply poly_act_assoc.
        }
        refine (_ @ poly_act_assoc _ _ _).
        apply maponpaths.
        etrans.
        {
          refine (!_).
          apply (functor_comp
                   (sem_endpoint_grpd_data_functor e₂ _)).
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (functor_comp
                   (sem_endpoint_grpd_data_functor e₂ _)).
        }
        refine (!_).
        apply maponpaths.
        apply IHe₁.
      - (* Left inclusion *)
        exact (poly_act_id_right _ @ !(poly_act_id_left _)).
      - (* Right inclusion *)
        exact (poly_act_id_right _ @ !(poly_act_id_left _)).
      - (* Left projection *)
        exact (poly_act_id_right _ @ !(poly_act_id_left _)).
      - (* Right projection *)
        exact (poly_act_id_right _ @ !(poly_act_id_left _)).
      - (* Pairing *)
        exact (pathsdirprod (IHe₁ _ _ _) (IHe₂ _ _ _)).
      - (* Constant *)
        exact (idpath _).
      - (* Constant map *)
        apply pathscomp0rid.
      - (* Constructor *)
        simpl.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply iso_after_iso_inv.
        }
        etrans.
        {
          apply id_right.
        }
        do 2 apply maponpaths.
        apply univ1_functor_data_help_eq_constr.
    Qed.

    Definition univ1_functor_data_help_homot_endpoint_ap
               {T₁ T₂ : poly_code}
               (e : endpoint (point_constr Σ) T₁ T₂)
               {x y : poly_act T₁ (poly_initial (point_constr Σ))}
               (p : poly_act_rel
                      T₁
                      (initial_groupoid_algebra_mor_el_poly (path_left Σ) (path_right Σ) I)
                      x y)
      : poly_act_compose
          (univ1_functor_data_endpoint
             e
             x)
          (poly_act_compose
             (sem_endpoint_grpd_data_functor_morphism
                e (pr211 Y)
                (univ1_functor_data_help
                   (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
                      p)))
             (poly_act_inverse
                (univ1_functor_data_endpoint
                   e
                   y)))
        =
        univ1_functor_data_help
          (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
             (poly_act_rel_ap_endpoint e p)).
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q
                      | P Q R e₁ IHe₁ e₂ IHe₂
                      | P T t | C₁ C₂ g | ].
      - simpl.
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }        
        apply poly_act_id_right.
      - simpl.
        refine (_ @ IHe₂ _ _ _) ; clear IHe₂.
        refine (!(poly_act_assoc _ _ _) @ _).
        apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          apply poly_act_inverse_compose.
        }
        do 2 refine (poly_act_assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(IHe₁ _ _ _)).
        }
        clear IHe₁.
        etrans.
        {
          apply (functor_comp (sem_endpoint_grpd e₂ (_ ,, pr211 Y))).
        }
        etrans.
        {
          apply maponpaths.
          apply (functor_comp (sem_endpoint_grpd e₂ (_ ,, pr211 Y))).
        }
        cbn.
        refine (poly_act_assoc _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply (poly_act_inverse_functor (sem_endpoint_grpd e₂ (_ ,, pr211 Y))).
        }
        simpl.
        apply maponpaths.
        apply poly_act_id_right.
      - simpl.
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }        
        apply poly_act_id_right.
      - simpl.
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }        
        apply poly_act_id_right.
      - simpl.
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }        
        apply poly_act_id_right.
      - simpl.
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }        
        apply poly_act_id_right.
      - simpl.
        apply pathsdirprod.
        + apply IHe₁.
        + apply IHe₂.
      - apply idpath.
      - induction p.
        apply idpath.
      - simpl.
        refine (assoc _ _ _ @ _).
        do 2 apply maponpaths.
        use subtypePath.
        { intro ; apply isaprop_is_iso. }
        apply idpath.
    Qed.
      
    Definition univ1_functor_data_help_homot_endpoint
               {Q : poly_code}
               {TR : poly_code}
               {al ar : endpoint (point_constr Σ) Q TR}
               {T : poly_code}
               {sl sr : endpoint (point_constr Σ) Q T}
               (p : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
               (z : poly_act Q (initial_groupoid_algebra_ob Σ))
               (p_arg :
                  poly_act_rel
                    TR
                    initial_groupoid_algebra_mor_el
                    (sem_endpoint_UU
                       al
                       (poly_initial_alg (point_constr Σ))
                       z)
                    (sem_endpoint_UU
                       ar
                       (poly_initial_alg (point_constr Σ))
                       z))
      : univ1_functor_data_help
          (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
             (sem_homot_endpoint_initial p z p_arg))
        =
        poly_act_compose
          (univ1_functor_data_endpoint sl _)
          (poly_act_compose
             (sem_homot_endpoint_grpd
                p
                (pr11 Y) (pr21 Y)
                (poly_map
                   Q
                   (poly_initial_rec
                      (point_constr Σ)
                      (pr111 (pr1 Y))
                      (pr121 (pr1 Y)))
                   z)
                (poly_act_compose
                   (poly_act_inverse (univ1_functor_data_endpoint al z))
                   (poly_act_compose
                      (univ1_functor_data_help
                         (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly p_arg))
                  (univ1_functor_data_endpoint ar z))))
             (poly_act_inverse
                (univ1_functor_data_endpoint sr _))).
    Proof.
      induction p as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                      | T₁ T₂ e₁ e₂ e₃
                      | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                      | P R e₁ e₂ | P R e₁ e₂
                      | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                      | P₁ P₂ P₃ e₁ e₂ e₃
                      | W w T e
                      | j e | ].
      - simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply poly_act_inv_right.
        }
        exact (!(univ1_functor_data_help_eq_id _)).
      - simpl.
        refine (_ @ maponpaths poly_act_inverse IHh @ _).
        + apply univ1_functor_data_help_eq_inv.
        + etrans.
          {
            apply poly_act_inverse_compose.
          }
          etrans.
          {
            apply maponpaths_2.
            apply poly_act_inverse_compose.
          }
          refine (!(poly_act_assoc _ _ _) @ _).
          apply maponpaths_2.
          apply poly_act_inverse_inverse.
      - simpl.
        refine (_ @ maponpaths (λ z, poly_act_compose z _) IHh₁
                  @ maponpaths (λ z, poly_act_compose _ z) IHh₂
                  @ _).
        + apply univ1_functor_data_help_eq_comp.
        + refine (!(poly_act_assoc _ _ _) @ _).
          apply maponpaths.
          do 2 refine (poly_act_assoc _ _ _ @ _).
          do 2 apply maponpaths_2.
          refine (!(poly_act_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply poly_act_inv_left.
          }
          apply poly_act_id_right.
      - simpl.
        refine (!_).
        etrans.
        {
          etrans.
          {
            refine (!_).
            apply poly_act_assoc.
          }
          apply maponpaths.
          etrans.
          {
            do 2 apply maponpaths.
            apply poly_act_inverse_compose.
          }
          do 2 refine (poly_act_assoc _ _ _ @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply (functor_comp (sem_endpoint_grpd e₃ (_ ,, pr211 Y))).
          }
          simpl.
          etrans.
          {
            apply maponpaths.
            apply (poly_act_inverse_functor
                     (sem_endpoint_grpd e₃ (_ ,, pr211 Y))).
          }
          simpl.
          etrans.
          {
            refine (!_).
            apply (functor_comp (sem_endpoint_grpd e₃ (_ ,, pr211 Y))).
          }
          cbn.
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply poly_act_id_right.
          }
          refine (!(poly_act_assoc _ _ _) @ _).
          exact (!IHp).
        }
        clear IHp.
        apply univ1_functor_data_help_homot_endpoint_ap.
      - simpl.
        etrans.
        {
          apply univ1_functor_data_help_eq_id.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply poly_act_inverse_compose.
          }
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply (functor_comp (sem_endpoint_grpd_data_functor e₃ _)).
          }
          simpl.
          apply poly_act_inverse_compose.
        }
        etrans.
        {
          refine (poly_act_assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (poly_act_assoc _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            refine (!(poly_act_assoc _ _ _) @ _).
            etrans.
            {
              apply maponpaths.
              apply poly_act_inv_right.
            }
            apply poly_act_id_right.
          }
          refine (!(poly_act_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply poly_act_inv_right.
          }
          apply poly_act_id_right.
        }
        apply poly_act_inv_right.
      - simpl.
        etrans.
        {
          apply univ1_functor_data_help_eq_id.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply (functor_id (sem_endpoint_grpd_data_functor e _)).
          }
          apply poly_act_id_right.
        }
        apply poly_act_inv_right.
      - simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths_2.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply poly_act_inv_right.
        }
        exact (!(univ1_functor_data_help_eq_id _)).        
      - simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths_2.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply poly_act_inv_right.
        }
        exact (!(univ1_functor_data_help_eq_id _)).        
      - simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths_2.
          apply poly_act_id_left.
        }
        etrans.
        {
          apply poly_act_inv_right.
        }
        exact (!(univ1_functor_data_help_eq_id _)).        
      - exact (pathsdirprod IHh₁ IHh₂).
      - simpl.
        apply pathsdirprod.
        + refine (!_).
          etrans.
          {
            apply maponpaths.
            apply poly_act_id_left.
          }
          etrans.
          {
            apply poly_act_inv_right.
          }
          exact (!(univ1_functor_data_help_eq_id _)).        
        + refine (!_).
          etrans.
          {
            apply maponpaths.
            apply poly_act_id_left.
          }
          etrans.
          {
            apply poly_act_inv_right.
          }
          exact (!(univ1_functor_data_help_eq_id _)).        
      - apply idpath.
      - simpl.
        refine (_ @ assoc _ _ _).
        apply maponpaths.
        refine (_ @ assoc' _ _ _).
        use iso_inv_on_left.
        simpl.
        refine (!_).
        etrans.
        {
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            apply iso_after_iso_inv.
          }
          apply id_left.
        }
        refine (!_).
        apply (pr2 (pr21 Y j)).
      - simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!(poly_act_assoc _ _ _) @ _).
          apply maponpaths.
          etrans.
          {
            refine (!(poly_act_assoc _ _ _) @ _).
            apply maponpaths.
            apply poly_act_inv_right.
          }
          apply poly_act_id_right.
        }
        etrans.
        {
          refine (poly_act_assoc _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            apply poly_act_inv_right.
          }
          apply poly_act_id_left.
        }
        apply idpath.
    Qed.

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
                       | x
                       | x y z f g
                       | P Q x y f g r IHr
                       |
                       |
                       | P Q x y f g r IHr
                       |
                       |
                       | 
                       | P Q x₁ y₁ x₂ y₂ f₁ f₂ g₁ g₂ r₁ IHr₁ r₂ IHr₂
                       | 
                       | x y f₁ f₂ r IHr | P x y f₁ f₂ r IHr
                       | P x y z f₁ f₂ g r IHr
                       | P x y z f g₁ g₂ r IHr
                       | P x y f | | | |
                       | j x y p
                       | j z p].
      - apply idpath.
      - exact (!IHr).
      - exact (IHr₁ @ IHr₂).
      - simpl.
        refine (_
                @ iso_inv_after_iso
                    (idtoiso
                       (poly_initial_comp
                          (point_constr Σ)
                          (alg_carrier_grpd Y)
                          (pr121 (pr1 Y))
                          x))).
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (_ @ id_left _).
        apply maponpaths_2.
        refine (_ @ functor_id (pr211 Y) _).
        apply maponpaths.
        apply univ1_functor_data_help_eq_id.
      - simpl.
        refine (assoc' _ _ _ @ _).
        do 2 refine (_ @ assoc _ _ _).
        apply maponpaths.
        do 2 refine (_ @ assoc' _ _ _).
        apply maponpaths_2.
        refine (!_).
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply iso_after_iso_inv.
        }
        rewrite id_left.
        etrans.
        {
          refine (!_).
          apply functor_comp.
        }
        apply idpath.
      - exact IHr.
      - apply idpath.
      - apply idpath.
      - exact IHr.
      - apply idpath.
      - apply idpath.
      - apply idpath.
      - exact (pathsdirprod IHr₁ IHr₂).
      - apply idpath.
      - exact (maponpaths (λ z, (_ · # (pr211 Y : _ ⟶ _) z) · _) IHr).
      - exact (maponpaths poly_act_inverse IHr). 
      - exact (maponpaths (λ z, poly_act_compose z _) IHr).
      - exact (maponpaths (poly_act_compose _) IHr).
      - apply poly_act_id_right.
      - apply poly_act_id_left.
      - apply poly_act_assoc.
      - apply poly_act_inv_right.
      - apply poly_act_inv_left.
      - simpl.
        refine (!_).
        etrans.
        {
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          exact (univ1_functor_data_help_eq_natural (path_left Σ j) p).
        }
        refine (assoc' _ _ _ @ _).
        refine (_ @ assoc _ _ _).
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply (nat_trans_ax (pr21 Y j)).
        }
        refine (assoc' _ _ _ @ _).
        refine (_ @ assoc _ _ _).
        apply maponpaths.
        refine (!_).
        use iso_inv_on_right ; simpl.
        refine (_ @ assoc' _ _ _).
        use iso_inv_on_left ; simpl.
        refine (!_).
        exact (univ1_functor_data_help_eq_natural (path_right Σ j) p).
      - refine (univ1_functor_data_help_homot_endpoint _ _ _ @ _).
        refine (_ @ !(univ1_functor_data_help_homot_endpoint _ _ _)).
        apply maponpaths.
        apply maponpaths_2.
        apply (pr2 Y j (poly_map _ (poly_initial_rec _ _ (pr1 (pr211 Y))) z)).
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

    Definition poly_act_functor_morphisms_inv
               (P : poly_code)
               {x y : poly_act P (alg_carrier_grpd (initial_groupoid_algebra Σ))}
               (p : poly_act_morphism
                      P
                      (alg_carrier_grpd (initial_groupoid_algebra Σ))
                      x y)
      : poly_act_functor_morphisms
          P univ1_functor
          (poly_act_rel_inv
             P
             (initial_groupoid_algebra_mor Σ)
             (λ _ _ g,
              initial_groupoid_algebra_carrier_comp
                Σ (initial_groupoid_algebra_carrier_inv Σ g)
                (initial_groupoid_algebra_carrier_id Σ _))
             p)
        =
        poly_act_inverse
          (poly_act_functor_morphisms
             P univ1_functor
             p).
    Proof.
      induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
      - apply idpath.
      - revert p.
        use (setquotunivprop _ (λ _, make_hProp _ _)).
        + apply homset_property.
        + intro z.
          apply id_right.
      - induction x as [x | x], y as [y | y].
        + apply IHP₁.
        + induction p.
        + induction p.
        + apply IHP₂.
      - exact (pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _)).
    Qed.

    Definition univ1_is_nat_trans_help
               {x y : poly_act_groupoid
                        (point_constr Σ)
                        (initial_groupoid_algebra_carrier Σ)}
               (i : initial_groupoid_algebra_mor_el_poly
                      (path_left Σ) (path_right Σ)
                      (point_constr Σ)
                      x y)
      : univ1_functor_data_help i
        =
        poly_act_functor_morphisms
          (point_constr Σ)
          univ1_functor
          (quot_rel_poly_act
             (initial_groupoid_algebra_mor_el_eqrel Σ)
             (setquotpr
                (poly_act_eqrel
                   (point_constr Σ)
                   (initial_groupoid_algebra_mor_el_eqrel Σ) x y)
                (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel i))).
    Proof.
      induction i as [ P x | P x y f IHf |
                       P x y z f₁ IHf₁ f₂ IHf₂
                       | j x
                       | P Q x y f IHf | P Q x y f IHf
                       | P Q x₁ x₂ y₁ y₂ f₁ IHf₁ f₂ IHf₂
                       | x y f IHf].
      - simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply quot_rel_poly_act_identity.
        }
        apply (functor_id (poly_act_functor P univ1_functor)).
      - etrans.
        {
          exact (maponpaths poly_act_inverse IHf).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          simpl.
          apply quot_rel_poly_act_inv.
        }
        apply poly_act_functor_morphisms_inv.
      - simpl.
        etrans.
        {
          apply maponpaths.
          exact IHf₂.
        }
        etrans.
        {
          apply maponpaths_2.
          exact IHf₁.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply quot_rel_poly_act_comp.
        }
        apply (functor_comp (poly_act_functor P univ1_functor)).
      - apply idpath.
      - refine (IHf @ _).
        simpl.
        do 2 apply maponpaths.
        apply setquotpr_eq.
      - refine (IHf @ _).
        simpl.
        do 2 apply maponpaths.
        apply setquotpr_eq.
      - exact (pathsdirprod IHf₁ IHf₂).
      - apply idpath.
    Qed.

    Definition univ1_is_nat_trans
      : is_nat_trans _ _ univ1_commute_data.
    Proof.
      intros x y f.
      simpl in f.
      cbn -[univ1_functor].
      unfold univ1_commute_data.
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
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              unfold initial_groupoid_algebra_point_constr_data_morph.
              apply setquotuniv'_comm.
            }
            exact (setquotunivcomm
                     (initial_groupoid_algebra_mor_el_eqrel
                        Σ
                        (poly_initial_alg (point_constr Σ) x)
                        (poly_initial_alg (point_constr Σ) y))
                     (make_hSet _ _)
                     _
                     _
                     (initial_alg_ap
                        (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly f))).
          }
          simpl.
          do 2 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply iso_after_iso_inv.
          }
          etrans.
          {
            apply id_right.
          }
          apply maponpaths.
          refine (!_).
          etrans.
          {
            do 3 apply maponpaths.
            refine (!_).
            apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec.
          }
          refine (!_).
          apply univ1_is_nat_trans_help.
      }
      refine (X _ @ _).
      do 3 apply maponpaths.
      apply quot_rel_poly_act_poly_act_quot_rel.
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

  (* Lemma for univ2 *)
  Definition functor_initial_alg_inv
             (Y : hit_algebra_grpd Σ)
             (f : initial_groupoid_algebra Σ --> Y)
             {x y : initial_groupoid_algebra_ob Σ}
             (p : initial_groupoid_algebra_mor_el_poly
                    (path_left Σ) (path_right Σ)
                    I
                    x y)

    : # (pr111 (pr1 f))
        (setquotpr
           (initial_groupoid_algebra_mor_el_eqrel Σ y x)
           (initial_alg_inv p))
      =
      grpd_inv
        (# (pr111 (pr1 f))
           (setquotpr
              (initial_groupoid_algebra_mor_el_eqrel Σ x y)
              p)).
  Proof.
    use is_grpd_inv.
    etrans.
    {
      exact (!(functor_comp (pr11 (pr1 f)) _ _)).
    }
    refine (_ @ functor_id _ _).
    apply maponpaths.
    apply iscompsetquotpr.
    apply hinhpr.
    apply initial_alg_left_inv.
  Qed.
  
  Section Univ2.
    Variable (Y : hit_algebra_grpd Σ)
             (f g : initial_groupoid_algebra Σ --> Y).

    (** Needs to be more compositional *)
    Definition initial_groupoid_algebra_univ_2_nat_trans_data
      : nat_trans_data (pr111 (pr1 f)) (pr111 (pr1 g)).
    Proof.
      use poly_initial_ind.
      simpl ; intros x Hx.
      pose (pr11 (pr211 f) x) as m ; simpl in m.
      refine (m · _) ; clear m.
      pose (pr11 (pr211 g) x) as m ; simpl in m.
      refine (_ · grpd_inv m).
      clear m.
      refine (#(pr211 Y : _ ⟶ _) _) ; simpl.
      exact (initial_groupoid_algebra_univ_2_nat_trans_data_help Hx).
    Defined.

    Definition initial_groupoid_algebra_univ_2_nat_trans_data_help_endpoint
               {P Q : poly_code}
               (e : endpoint (point_constr Σ) P Q)
               (x : poly_act P (poly_initial (point_constr Σ)))
      : initial_groupoid_algebra_univ_2_nat_trans_data_help
          (poly_dmap
             Q
             _
             (initial_groupoid_algebra_univ_2_nat_trans_data)
             (sem_endpoint_UU e (poly_initial_alg (point_constr Σ)) x))
        =
        poly_act_compose
          (sem_endpoint_grpd_natural e (pr11 f) x)
          (poly_act_compose
             (# (sem_endpoint_grpd_data_functor e (pr11 Y))
                (poly_act_nat_trans_data_help
                   P
                   initial_groupoid_algebra_univ_2_nat_trans_data
                   x))
             (poly_act_inverse
                (sem_endpoint_grpd_natural e (pr11 g) x))).
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q
                      | P Q R e₁ IHe₁ e₂ IHe₂
                      | P T t | C₁ C₂ h | ].
      - simpl.
        refine (!_).
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }
        etrans.
        {
          apply poly_act_id_right.
        }
        refine (!_).
        apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
      - simpl.
        refine (IHe₂ _ @ _) ; clear IHe₂.
        simpl.
        refine (_ @ poly_act_assoc _ _ _).
        apply maponpaths.
        refine (_ @ !(poly_act_assoc _ _ _)).
        refine (!_).        
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_compose.
        }
        refine (poly_act_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (functor_comp (sem_endpoint_grpd_data_functor e₂ (pr11 Y))).
        }
        cbn.
        etrans.
        {
          apply maponpaths.
          apply (poly_act_inverse_functor
                   (sem_endpoint_grpd_data_functor e₂ (pr11 Y))).
        }
        simpl.
        etrans.
        {
          refine (!_).
          apply (functor_comp (sem_endpoint_grpd_data_functor e₂ (pr11 Y))).
        }
        cbn.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_right.
        }
        refine (!(poly_act_assoc _ _ _) @ _).
        refine (!(IHe₁ x) @ _) ; clear IHe₁.
        apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
      - simpl.
        refine (!_).
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }
        etrans.
        {
          apply poly_act_id_right.
        }
        refine (!_).
        apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
      - simpl.
        refine (!_).
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }
        etrans.
        {
          apply poly_act_id_right.
        }
        refine (!_).
        apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
      - simpl.
        refine (!_).
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }
        etrans.
        {
          apply poly_act_id_right.
        }
        refine (!_).
        apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
      - simpl.
        refine (!_).
        etrans.
        {
          apply poly_act_id_left.
        }
        etrans.
        {
          apply maponpaths.
          apply poly_act_inverse_identity.
        }
        etrans.
        {
          apply poly_act_id_right.
        }
        refine (!_).
        apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
      - exact (pathsdirprod (IHe₁ _) (IHe₂ _)).
      - apply idpath.
      - apply idpath.
      - simpl.
        unfold initial_groupoid_algebra_univ_2_nat_trans_data.
        rewrite poly_initial_ind_comp.
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
    Qed.
    
    Definition initial_groupoid_algebra_univ_2_is_nat_trans_help_arg
               {P : poly_code}
               {x y : poly_act
                        P
                        (initial_groupoid_algebra_ob_poly (point_constr Σ))}
               (p : initial_groupoid_algebra_mor_el_poly
                      (path_left Σ) (path_right Σ)
                      P
                      x y)
      : poly_act_morphism P (initial_groupoid_algebra_carrier Σ) x y.
    Proof.
      apply quot_rel_poly_act.
      apply setquotpr.
      exact (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel p).
    Defined.

    Definition initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_spec
               {x y : poly_act
                        (point_constr Σ)
                        (initial_groupoid_algebra_ob_poly (point_constr Σ))}
               (p : initial_groupoid_algebra_mor_el_poly
                      (path_left Σ) (path_right Σ)
                      (point_constr Σ)
                      x y)
      : setquotpr
          (initial_groupoid_algebra_mor_el_eqrel
             Σ
             (poly_initial_alg (point_constr Σ) x)
             (poly_initial_alg (point_constr Σ) y))
          (initial_alg_ap p)
        =
        initial_groupoid_algebra_point_constr_data_morph
          Σ
          (poly_act_quot_rel
             (initial_groupoid_algebra_mor_el_eqrel Σ)
             (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p)).
    Proof.
      unfold initial_groupoid_algebra_univ_2_is_nat_trans_help_arg.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply poly_act_quot_rel_quot_rel_poly_act.
      }
      apply iscompsetquotpr.
      apply hinhpr.
      apply initial_alg_ap2.
      cbn.
      apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_alt.
    Qed.

    Definition initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_id
               {P : poly_code}
               (x : poly_act_groupoid P (pr111 (initial_groupoid_algebra Σ)))
      : initial_groupoid_algebra_univ_2_is_nat_trans_help_arg (initial_alg_id x)
        =
        poly_act_identity x.
    Proof.
      induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
      - apply idpath.
      - cbn.
        apply setquotpr_eq.
      - induction x as [x | x].
        + refine (_ @ IHP₁ x).
          unfold initial_groupoid_algebra_univ_2_is_nat_trans_help_arg.
          simpl.
          apply maponpaths.
          cbn.
          apply setquotpr_eq.
        + refine (_ @ IHP₂ x).
          unfold initial_groupoid_algebra_univ_2_is_nat_trans_help_arg.
          simpl.
          apply maponpaths.
          cbn.
          apply setquotpr_eq.
      - exact (pathsdirprod (IHP₁ _) (IHP₂ _)).
    Qed.

    Definition initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_inv
               {P : poly_code}
               {x y : poly_act
                        P
                        (initial_groupoid_algebra_ob_poly (point_constr Σ))}
               (p : initial_groupoid_algebra_mor_el_poly
                      (path_left Σ) (path_right Σ)
                      P
                      x y)
      : initial_groupoid_algebra_univ_2_is_nat_trans_help_arg (initial_alg_inv p)
        =
        poly_act_inverse (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p).
    Proof.
      apply quot_rel_poly_act_inv.
    Qed.    

    Definition initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_comp
               {P : poly_code}
               {x y z : poly_act
                          P
                          (initial_groupoid_algebra_ob_poly (point_constr Σ))}
               (p₁ : initial_groupoid_algebra_mor_el_poly
                       (path_left Σ) (path_right Σ)
                       P
                       x y)
               (p₂ : initial_groupoid_algebra_mor_el_poly
                       (path_left Σ) (path_right Σ)
                       P
                       y z)
      : initial_groupoid_algebra_univ_2_is_nat_trans_help_arg (initial_alg_comp p₁ p₂)
        =
        poly_act_compose
          (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p₁)
          (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p₂).
    Proof.
      apply quot_rel_poly_act_comp.
    Qed.
      
    Definition initial_groupoid_algebra_univ_2_is_nat_trans_help
               {P : poly_code}
               {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
               (p : initial_groupoid_algebra_mor_el_poly
                      (path_left Σ) (path_right Σ)
                      P
                      x y)
      : poly_act_compose
          (poly_act_functor_morphisms
             P
             (pr111 f)
             (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p))
          (poly_act_nat_trans_data_help
             P
             initial_groupoid_algebra_univ_2_nat_trans_data
             y)
        =
        poly_act_compose
          (poly_act_nat_trans_data_help
             P
             initial_groupoid_algebra_univ_2_nat_trans_data
             x)
          (poly_act_functor_morphisms
             P
             (pr111 g)
             (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p)).
    Proof.
      induction p as [ P x | P x y p IHp | P x y z p₁ IHp₁ p₂ IHp₂
                       | j x | P Q x y p IHp | P Q x y p IHp
                       | P Q x₁ y₁ x₂ y₂ p₁ IHp₁ p₂ IHp₂
                       | x y p IHp ].
      - refine (_ @ poly_act_id_left _ @ !(poly_act_id_right _) @ _).
        + apply maponpaths_2.
          refine (_ @ functor_id (poly_act_functor P (pr111 f)) x).
          apply maponpaths.
          exact (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_id x).
        + apply maponpaths.
          refine (!_).
          refine (_ @ functor_id (poly_act_functor P (pr111 g)) x).
          apply maponpaths.
          exact (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_id x).
      - refine (_ @ poly_act_id_left _).
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(poly_act_inv_left
                     (poly_act_functor_morphisms
                        P
                        (pr111 f)
                        (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p)))).
        }
        refine (!(poly_act_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          refine (poly_act_assoc _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            exact IHp.
          }
          refine (!(poly_act_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply maponpaths.
              apply initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_inv.
            }
            refine (!(functor_comp (poly_act_functor P (pr111 g)) _ _) @ _).
            etrans.
            {
              apply maponpaths.
              apply poly_act_inv_right.
            }
            exact (functor_id (poly_act_functor P (pr111 g)) _).
          }
          apply poly_act_id_right.
        }
        apply maponpaths_2.
        refine (poly_act_inverse_functor (poly_act_functor P (pr111 f)) _ @ _).
        apply maponpaths.
        refine (_ @ !(initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_inv _)).
        refine (!_).
        use (@is_grpd_inv
                 (poly_act_groupoid
                    P
                    (initial_groupoid_algebra_carrier Σ))).
        apply poly_act_inv_right.
      - etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_comp.
        }
        etrans.
        {
          apply maponpaths_2.
          exact (functor_comp
                   (poly_act_functor P (pr111 f))
                   (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p₁)
                   (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p₂)).
        }
        refine (!(poly_act_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          apply IHp₂.
        }
        refine (poly_act_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply IHp₁.
        }
        refine (!(poly_act_assoc _ _ _) @ _).
        apply maponpaths.
        refine (!(functor_comp
                    (poly_act_functor P (pr111 g))
                    (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p₁)
                    (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p₂)) @ _).
        apply maponpaths.
        refine (!_).
        apply initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_comp.
      - cbn.
        etrans.
        {
          apply maponpaths.
          apply (initial_groupoid_algebra_univ_2_nat_trans_data_help_endpoint
                   (path_right Σ j)).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply (initial_groupoid_algebra_univ_2_nat_trans_data_help_endpoint
                   (path_left Σ j)).
        }
        refine (!_).
        refine (assoc _ _ _ @ _).
        cbn.
        etrans.
        {
          apply maponpaths_2.
          refine (_ @ grpd_map_path_rule_pointwise f j x).
          cbn.
          apply maponpaths_2.
          apply maponpaths.
          apply setquotpr_eq.
        }
        refine (assoc' _ _ _ @ _ @ assoc _ _ _).
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (pr21 Y j)).
        }
        refine (assoc' _ _ _ @ _ @ assoc _ _ _).
        apply maponpaths.
        refine (!_).
        use iso_inv_on_right.
        refine (_ @ assoc' _ _ _).
        use iso_inv_on_left.
        refine (!_).
        simpl.
        refine (_ @ grpd_map_path_rule_pointwise g j x).
        cbn.
        apply maponpaths_2.
        apply maponpaths.
        apply setquotpr_eq.
      - simpl.
        refine (_ @ IHp @ _).
        + apply maponpaths_2.
          unfold initial_groupoid_algebra_univ_2_is_nat_trans_help_arg.
          do 2 apply maponpaths.
          apply setquotpr_eq.
        + apply maponpaths.
          refine (!_).
          unfold initial_groupoid_algebra_univ_2_is_nat_trans_help_arg.
          do 2 apply maponpaths.
          apply setquotpr_eq.
      - simpl.
        refine (_ @ IHp @ _).
        + apply maponpaths_2.
          unfold initial_groupoid_algebra_univ_2_is_nat_trans_help_arg.
          do 2 apply maponpaths.
          apply setquotpr_eq.
        + apply maponpaths.
          refine (!_).
          unfold initial_groupoid_algebra_univ_2_is_nat_trans_help_arg.
          do 2 apply maponpaths.
          apply setquotpr_eq.
      - exact (pathsdirprod IHp₁ IHp₂).
      - cbn -[initial_groupoid_algebra_univ_2_nat_trans_data] ; unfold idfun.
        unfold initial_groupoid_algebra_univ_2_nat_trans_data.
        rewrite !poly_initial_ind_comp.
        fold initial_groupoid_algebra_univ_2_nat_trans_data.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (_ @ nat_trans_ax
                        (pr1 (pr211 f))
                        x y
                        (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p))
          ; cbn.
          apply maponpaths_2.
          apply maponpaths.
          refine (_ @ initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_spec _).
          cbn.
          apply setquotpr_eq.
        }
        cbn.
        refine (assoc' _ _ _ @ _).
        refine (_ @ assoc _ _ _).
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          exact (!(functor_comp (pr211 Y) _ _)).
        }                  
        refine (!_).
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (_ @ grpd_inv_nat_trans_ax
                        (pr1 (pr211 g))
                        (initial_groupoid_algebra_univ_2_is_nat_trans_help_arg p))
          ; cbn.
          do 2 apply maponpaths.
          refine (_ @ initial_groupoid_algebra_univ_2_is_nat_trans_help_arg_spec _).
          cbn.
          apply setquotpr_eq.
        }
        cbn.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!(functor_comp (pr211 Y) _ _) @ _).
        apply maponpaths.
        simpl in IHp.
        cbn.
        refine (!_).
        refine (_ @ IHp @ _).
        + apply maponpaths.
          apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
        + apply maponpaths_2.
          refine (!_).
          apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
    Qed.
    
    Definition initial_groupoid_algebra_univ_2_is_nat_trans
      : is_nat_trans _ _ initial_groupoid_algebra_univ_2_nat_trans_data.
    Proof.
      intros x y.
      use (setquotunivprop _ (λ _, make_hProp _ _)).
      { apply homset_property. }
      intro p.
      cbn.
      refine (_ @ initial_groupoid_algebra_univ_2_is_nat_trans_help p @ _).
      - apply maponpaths_2.
        apply maponpaths.
        unfold initial_groupoid_algebra_mor_el in p.
        cbn.
        etrans.
        {
          refine (!_).
          exact (iscompsetquotpr
                   (initial_groupoid_algebra_mor_el_eqrel Σ x y)
                   _
                   _
                   (hinhpr
                      (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_alt p))).
        }
        apply setquotpr_eq.
      - do 2 apply maponpaths.
        cbn.
        refine (!_).
        etrans.
        {
          refine (!_).
          exact (iscompsetquotpr
                   (initial_groupoid_algebra_mor_el_eqrel Σ x y)
                   _
                   _
                   (hinhpr
                      (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_alt p))).
        }
        apply setquotpr_eq.
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
      unfold initial_groupoid_algebra_univ_2_nat_trans_data.
      rewrite poly_initial_ind_comp.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply iso_after_iso_inv.
      }
      etrans.
      {
        apply id_right.
      }
      apply maponpaths.
      apply initial_groupoid_algebra_univ_2_nat_trans_data_help_poly_dmap.
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
    use poly_initial_ind.
    cbn ; intros x Hx.
    pose (nat_trans_eq_pointwise (pr211 p) x) as h₁.
    pose (nat_trans_eq_pointwise (pr211 q) x) as h₂.
    pose (cancel := pr11 (pr211 g) x).
    apply (groupoid_cancel _ _ cancel).
    refine (h₁ @ _ @ !h₂).
    clear cancel h₁ h₂.
    refine (maponpaths (λ z, _ · # (pr121 (pr1 Y)) z) _) ; simpl.
    exact (initial_groupoid_algebra_univ_eq_help (point_constr Σ) Hx).
  Qed.
  
  Definition initial_groupoid_algebra_is_initial
    : unique_maps (initial_groupoid_algebra Σ).
  Proof.
    use make_unique_maps.
    - exact initial_groupoid_algebra_univ_1.
    - exact initial_groupoid_algebra_univ_2.
    - exact initial_groupoid_algebra_univ_eq.
  Defined.
End GrpdAlgUMP.
