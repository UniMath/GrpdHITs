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
Require Import algebra.one_types_polynomials.
Require Import displayed_algebras.displayed_algebra.

Require Import initial_grpd_alg.W_poly.
Require Import initial_grpd_alg.relation_2.
Require Import initial_grpd_alg.initial_groupoid_algebra.

Local Open Scope cat.

Local Arguments nat_trans_comp {_ _ _ _ _} _ _.

Local Definition TODO {A : Type} : A.
Admitted.

Definition grpd_inv
           {G : groupoid}
           {x y : G}
           (f : x --> y)
  : y --> x
  := inv_from_iso (make_iso f (pr2 G _ _ f)).

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
    (*
    Definition lol
               {Q TR T : poly_code}
               {al ar : endpoint (point_constr Σ) Q TR}
               {el er : endpoint (point_constr Σ) Q T}
               (h : homot_endpoint
                      (path_left Σ)
                      (path_right Σ)
                      al ar
                      el er)
               (z : poly_act
                      Q
                      (initial_groupoid_algebra_ob Σ))
               (p : poly_act_morphism
                      TR
                      (pr111 Y)
                      (sem_endpoint_UU
                         al
                         (pr1 (pr211 Y))
                         (poly_map
                            Q
                            (poly_initial_rec
                               (point_constr Σ)
                               (pr111 (pr1 Y))
                            (pr121 (pr1 Y)))
                         z))
               (sem_endpoint_UU
                  ar
                  (pr1 (pr211 Y))
                  (poly_map
                     Q
                     (poly_initial_rec
                        (point_constr Σ)
                        (pr111 (pr1 Y))
                        (pr121 (pr1 Y)))
                     z)))
      : poly_act_compose
          (poly_act_rel_map
             (poly_initial_rec (point_constr Σ) (alg_carrier_grpd Y) (pr121 (pr1 Y)))
             (@univ1_functor_data_help I)
             TODO)
          (univ1_functor_data_endpoint er z)
        =
        poly_act_compose
          (univ1_functor_data_endpoint el z)
          (sem_homot_endpoint_grpd
             h
             (pr11 Y)
             (pr21 Y)
             (poly_map
                Q
                (poly_initial_rec (point_constr Σ) (pr111 (pr1 Y)) (pr121 (pr1 Y)))
                z)
             p).
    Proof.
      induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                      | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                      | T₁ T₂ e₁ e₂ e₃ e₄ h IHh | T₁ T₂ e₁ e₂ e₃ e₄ h IHh
                      | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                      | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                      | j e | el er | ].
      - simpl.
        cbn.
        refine (!_).
        refine (poly_act_id_right _ @ !(poly_act_id_left _) @ _).
        apply maponpaths_2.
        refine (!_).
        apply TODO.
      - simpl.
        apply TODO.
      - simpl.
        refine (!_).
        etrans.
        {
          refine (poly_act_assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!_).
          apply IHh₁.
        }
        etrans.
        {
          refine (!(poly_act_assoc _ _ _) @ _).
          apply maponpaths.
          refine (!_).
          apply IHh₂.
        }
        clear IHh₁ IHh₂.
        refine (poly_act_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply TODO.
      - simpl.
        apply TODO.
      - apply TODO.
      - apply TODO.
      - simpl.
        simpl in IHh.
        apply TODO.
      - apply TODO.
      - simpl.
        apply TODO.
      - simpl.
        apply TODO.
      - simpl.
        apply TODO.
      - simpl.
        apply TODO.
      - simpl.
        apply TODO.
      - apply TODO.
    Qed.
        
        (*
    Definition lol
               {Q TR T : poly_code}
               {al ar : endpoint (point_constr Σ) Q TR}
               {el er : endpoint (point_constr Σ) Q T}
               (h : homot_endpoint
                      (path_left Σ)
                      (path_right Σ)
                      al ar
                      el er)
               (z : poly_act
                      Q
                      (initial_groupoid_algebra_ob Σ))
               (p : poly_act_rel
                      T
                      initial_groupoid_algebra_mor_el
                      (sem_endpoint_UU
                         el
                         (poly_initial_alg (point_constr Σ)) z)
                      (sem_endpoint_UU
                         er
                         (poly_initial_alg (point_constr Σ)) z))
      : poly_act_compose
          (poly_act_rel_map
             (poly_initial_rec (point_constr Σ) (alg_carrier_grpd Y) (pr121 (pr1 Y)))
             (λ _ _ g, univ1_functor_data_help g)
             p
          )
          (univ1_functor_data_endpoint er z)
        =
        poly_act_compose
          (univ1_functor_data_endpoint el z)
          (sem_homot_endpoint_grpd
             h
             (pr11 Y)
             (pr21 Y)
             (poly_map
                Q
                (poly_initial_rec (point_constr Σ) (pr111 (pr1 Y)) (pr121 (pr1 Y)))
                z)
             TODO).
    Proof.
      (*
      assert (poly_act_rel
                TR precategory_morphisms
                (sem_endpoint_UU
                   al
                   (pr211 Y : _ ⟶ _)
                   (poly_map
                      Q
                      (poly_initial_rec
                         (point_constr Σ)
                         (pr111 (pr1 Y))
                         (pr121 (pr1 Y)))
                      z))
                (sem_endpoint_UU
                   ar
                   (pr211 Y : _ ⟶ _)
                   (poly_map
                      Q
                      (poly_initial_rec
                         (point_constr Σ)
                         (pr111 (pr1 Y))
                         (pr121 (pr1 Y)))
                      z))).
      {
        apply TODO.
      }
       *)
      induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                      | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                      | T₁ T₂ e₁ e₂ e₃ e₄ h IHh | T₁ T₂ e₁ e₂ e₃ e₄ h IHh
                      | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                      | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                      | j e | el er | ].
      - (* identity *)
        simpl.
        refine (!_).
        etrans.
        {
          apply poly_act_id_right.
        }
        refine (!(poly_act_id_left _) @ _).
        apply maponpaths_2.
        refine (!_).
        apply TODO.
      - (* symmetry *)
        simpl.
        refine (!_).
        apply TODO.
      - (* transitivity *)
        simpl.
        (*
        refine (!_).
        etrans.
        {
          refine (poly_act_assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!_).
          apply IHh₁.
        }
        refine (!(poly_act_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply IHh₂.
        }
        refine (poly_act_assoc _ _ _ @ _).
        apply maponpaths_2.
         *)
        apply TODO.
      - (* associativity *)
        simpl.
        do 2 refine (_ @ poly_act_assoc _ _ _).
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          apply poly_act_id_right.
        }
        refine (!(poly_act_id_left _) @ _).
        etrans.
        {
          do 2 apply maponpaths.
          refine (!_).
          apply (functor_comp
                   (sem_endpoint_grpd_data_functor e₃ _)).
        }
        apply maponpaths_2.
        apply TODO.
      - (* left identity *)
        apply TODO.
      - (* right identity *)
        apply TODO.
      - (* first projection *)
        simpl.
        refine (IHh _ @ _).
        apply TODO.
      - (* second projection *)
        apply TODO.
      - (* pair of endpoints *)
        exact (pathsdirprod (IHh₁ _) (IHh₂ _)).
      - (* left inclusion *)
        simpl.
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_left.
        }        
        refine (IHh p @ _).
        refine (!_).
        apply maponpaths_2.
        apply poly_act_id_left.
      - (* right inclusion *)
        simpl.
        etrans.
        {
          apply maponpaths.
          apply poly_act_id_left.
        }        
        refine (IHh p @ _).
        refine (!_).
        apply maponpaths_2.
        apply poly_act_id_left.
      - (* path constructor *)
        apply TODO.
      - (* point constructor *)
        simpl.
        apply TODO.
      - (* path argument *)
        apply TODO.
    Qed.
     *)
     *)
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
                       | P Q x y f g r IHr
                       |
                       | P Q x₁ y₁ x₂ y₂ f₁ f₂ g₁ g₂ r₁ IHr₁ r₂ IHr₂                       
                       | x y z f g
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
      - exact IHr.
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
      - pose (pr2 Y j (poly_map _ (poly_initial_rec _ _ (pr1 (pr211 Y))) z))
          as r.
        simpl in r.
        simpl.
        (*
        assert (univ1_functor_data_help
                  (sem_homot_endpoint_initial (homot_left_path Σ j) z p)
                =
                univ1_functor_data_endpoint
                  (homot_left_endpoint Σ j)
                  _
                · sem_homot_endpoint_grpd
                    (homot_left_path Σ j)
                    (pr11 Y)
                    (pr21 Y)
                    (poly_map
                       (homot_point_arg Σ j)
                       (poly_initial_rec (point_constr Σ) (pr111 (pr1 Y)) (pr121 (pr1 Y)))
                       z)
                    TODO
                · inv_from_iso
                    (make_iso
                       (univ1_functor_data_endpoint
                          (homot_right_endpoint Σ j)
                          _)
                       TODO))
          as X1.
        {
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            exact (lol
                     (homot_left_path Σ j)
                     z
                     (sem_homot_endpoint_initial (homot_left_path Σ j) z p)).
          }
          simpl.
          refine (assoc' _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            apply (iso_inv_after_iso
                     (make_iso
                        (univ1_functor_data_endpoint (homot_right_endpoint Σ j) z)
                        TODO)).
          }
          apply id_right.
        }
        refine (X1 @ _).
        clear X1.
        assert (univ1_functor_data_help
               (sem_homot_endpoint_initial (homot_right_path Σ j) z p)
             =
             univ1_functor_data_endpoint
               (homot_left_endpoint Σ j)
               _
             · sem_homot_endpoint_grpd
                 (homot_right_path Σ j)
                 (pr11 Y)
                 (pr21 Y)
                 (poly_map
                    (homot_point_arg Σ j)
                    (poly_initial_rec (point_constr Σ) (pr111 (pr1 Y)) (pr121 (pr1 Y)))
                    z)
                 TODO
             · inv_from_iso
                 (make_iso
                    (univ1_functor_data_endpoint
                       (homot_right_endpoint Σ j)
                       _)
                    TODO)).
        {
          apply TODO.
        }
        refine (_ @ !X).
        clear X.
        apply maponpaths_2.
        apply maponpaths.
        apply r.*)
        apply TODO.
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

    Definition initial_groupoid_algebra_univ_2_is_nat_trans
      : is_nat_trans _ _ initial_groupoid_algebra_univ_2_nat_trans_data.
    Proof.
      unfold is_nat_trans.
      use poly_initial_ind.
      intros x Hx.
      use poly_initial_ind.
      intros y Hy.
      (*use (setquotunivprop _ (λ _, make_hProp _ _)).
      { apply homset_property. }
      simpl.*)
      intro p.
      simpl in p.
      unfold initial_groupoid_algebra_univ_2_nat_trans_data.
      rewrite !poly_initial_ind_comp.
      refine (assoc _ _ _ @ _).
      refine (!_).
      (*
      pose (λ h,
            @grpd_nat_trans_ax
              _ _ _ _
              (pr12 (pr211 f))
              y x
              h) as inf.
      simpl in inf.
      pose (nat_trans_ax (pr12 (pr211 g)) x y) as ing.
      simpl in ing.
       *)

      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply assoc'.
      }
      refine (!_).

      (*
      unshelve epose (_ : setquot
                            (poly_act_eqrel
                               (point_constr Σ)
                               (initial_groupoid_algebra_mor_el_eqrel Σ)
                               x y))
        as h.
      {
        apply setquotpr.
        simpl.
        apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel.
        unfold initial_groupoid_algebra_mor_el in p.
        apply TODO.
      }
       *)
      unshelve epose (_ : poly_act_morphism
                            (point_constr Σ)
                            (pr111 Y)
                            (poly_map (point_constr Σ) (pr111 f : _ ⟶ _) x)
                            (poly_map (point_constr Σ) (pr111 f : _ ⟶ _) y))
        as h.
      {
        simpl.
        cbn.
        apply TODO.
      }
      simpl.

      assert (# (pr111 (pr1 f))
                p
              · (pr112 (pr11 f)) y
              =
              (pr112 (pr11 f)) x
              · # (pr211 Y : _ ⟶ _)
                  h).
      {
        apply TODO.
      }
      (*
      assert (# (pr111 (pr1 f))
                (setquotpr
                   (initial_groupoid_algebra_mor_el_eqrel
                      Σ (poly_initial_alg (point_constr Σ) x)
                      (poly_initial_alg (point_constr Σ) y))
                   p)
              · (pr112 (pr11 f)) y
              =
              (pr112 (pr11 f)) x
              · # (pr211 Y : _ ⟶ _)
                  (poly_act_functor_morphisms
                     (point_constr Σ)
                     (pr111 f)
                     (quot_rel_poly_act
                        _
                        h)))
        as X.
      {
        pose (nat_trans_ax
                (pr12 (pr211 f))
                x y
                (quot_rel_poly_act (initial_groupoid_algebra_mor_el_eqrel Σ) h))
          as r.
        simpl in r.
        unfold initial_groupoid_algebra_point_constr_data_morph in r.
        simpl in r.
        rewrite poly_act_quot_rel_quot_rel_poly_act in r.
        cbn in r.
        apply TODO.
      }*)
      etrans.
      {
        apply maponpaths_2.
        apply X.
      }
      clear X.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      simpl.
      unshelve epose (_ : poly_act_morphism
                            (point_constr Σ)
                            (pr111 Y)
                            (poly_map (point_constr Σ) (pr111 g : _ ⟶ _) x)
                            (poly_map (point_constr Σ) (pr111 g : _ ⟶ _) y))
        as h'.
      {
        apply TODO.
      }
      
      assert (grpd_inv (pr112 (pr11 g) x)
              ·  # (pr111 (pr1 g))
                p
              =
              # (pr1 (pr211 Y)) h'
             · grpd_inv ((pr112 (pr11 g)) y))
        as X.
      {
        apply TODO.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact X.
      }
      refine (assoc _ _ _ @ _).
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      etrans.
      {
        refine (!_).
        apply (functor_comp (pr211 Y)).
      }
      refine (!_).
      etrans.
      {
        refine (!_).
        apply (functor_comp (pr211 Y)).
      }
      apply maponpaths.
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
