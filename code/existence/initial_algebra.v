(** Here we define the notion of a HIT *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.

Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.
Require Import displayed_algebras.total_algebra_map.
Require Import displayed_algebras.constant_display.

Local Open Scope cat.

Definition initial_algebra_is_HIT
           (Σ : hit_signature)
           (X : hit_algebra_one_types Σ)
  : is_initial Σ X → is_HIT Σ X.
Proof.
  intros HX Y.
  pose (is_biinitial_to_is_biinitial' _ _ HX) as HX'.
  use section_to_disp_alg_map.
  - apply HX.
    exact tt.
  - pose (is_biinitial'_2cell_property
            HX'
            X
            (pr111 (pr1 (HX (total_algebra Y))) tt · projection Y)
            (id₁ X))
      as b.
    refine (isotoid_2_1 _ b).
    apply is_univalent_2_hit_algebra_one_types.
Defined.

Local Definition TODO {A : UU} : A.
Admitted.

Definition HIT_2cell_property_help
           (P : poly_code)
           {X Y : UU}
           {f g : X → Y}
           {x : poly_act P X}
           (Hx : poly_dact_UU P (λ x, f x = g x) x)
  : poly_map P f x = poly_map P g x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact Hx.
  - induction x as [x | x].
    + exact (maponpaths inl (IHP₁ x Hx)).
    + exact (maponpaths inr (IHP₂ x Hx)).
  - exact (pathsdirprod (IHP₁ _ (pr1 Hx)) (IHP₂ _ (pr2 Hx))).
Defined.

Definition HIT_2cell_property_help_is_poly_homot
           (P : poly_code)
           {X Y : UU}
           {f g : X → Y}
           (e : f ~ g)
           (x : poly_act P X)
  : HIT_2cell_property_help
      P
      (poly_dmap
         P (λ z, f z = g z) e x)
    =
    poly_homot P e x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (IHP₁ x)).
    + exact (maponpaths (maponpaths inr) (IHP₂ x)).
  - exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Defined.

Definition HIT_eq_property_help
           (P : poly_code)
           {X Y : UU}
           {f g : X → Y}
           {p q : ∏ (x : X), f x = g x}
           {x : poly_act P X}
           (Hx : poly_dact_UU P (λ x, p x = q x) x)
  : poly_homot P p x = poly_homot P q x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact Hx.
  - induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (IHP₁ x Hx)).
    + exact (maponpaths (maponpaths inr) (IHP₂ x Hx)).
  - exact (paths_pathsdirprod (IHP₁ _ (pr1 Hx)) (IHP₂ _ (pr2 Hx))).
Defined.

Section HITIsInitial.
  Context {Σ : hit_signature}
          (X : hit_algebra_one_types Σ)
          (HX : is_HIT Σ X).

  Definition HIT_1cell_property
    : biinitial_1cell_property X.
  Proof.
    intros Y.
    apply const_disp_alg_mor_to_alg_mor.
    apply HX.
  Defined.

  Variable (Y : hit_algebra_one_types Σ).

  Definition HIT_2cell_property_2cell
             (f g : X --> Y)
    : pr111 f ==> pr111 g.
  Proof.
    simple refine (pr1 (hit_ind_set HX _ _ _ _)).
    - exact (λ _, one_type_isofhlevel (pr111 Y) _ _).
    - simpl.
      intros x Hx.
      refine (pr1 (pr211 f) x @ _ @ !(pr1 (pr211 g) x)) ; cbn.
      apply (maponpaths (pr211 Y)).
      exact (HIT_2cell_property_help
               (point_constr Σ)
               Hx).
    - intros j x Hx ; simpl.
      apply map_PathOver.
      unfold square.
      simpl.
      apply TODO.
  Defined.

  Definition HIT_2cell_property_2cell_homomorph
             (f g : X --> Y)
    : (λ x, HIT_2cell_property_2cell f g ((pr211 X) x) @ (pr1 (pr211 g) x))
      =
      (λ x,
       (pr1 (pr211 f) x)
       @
       maponpaths
         (pr211 Y)
         (poly_homot (point_constr Σ) (HIT_2cell_property_2cell f g) x)).
  Proof.
    use funextsec ; intro x ; cbn ; simpl in x.
    unfold homotcomp, funhomotsec, homotfun.
    etrans.
    {
      apply maponpaths_2.
      exact (pr12 (hit_ind_set _ _ _ _ _) x).
    }
    simpl ; cbn.
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
    }
    apply maponpaths.
    apply HIT_2cell_property_help_is_poly_homot.
  Qed.

  Definition HIT_2cell_property
    : biinitial_2cell_property X Y.
  Proof.
    intros f g.
    use make_invertible_2cell.
    - simple refine (((_ ,, _) ,, (λ _, tt)) ,, tt).
      + exact (HIT_2cell_property_2cell f g).
      + exact (HIT_2cell_property_2cell_homomorph f g).
    - apply hit_alg_is_invertible_2cell_one_type.
  Defined.

  Definition HIT_eq_property
    : biinitial_eq_property X Y.
  Proof.
    intros f g α β.
    use subtypePath.
    { intro ; apply isapropunit. }
    use subtypePath.
    {
      intro.
      use impred ; intro.
      apply isapropunit.
    }
    use subtypePath.
    { intro ; apply one_types. }
    use funextsec.
    simple refine (pr1 (hit_ind_prop HX _ _ _)).
    - intros x.
      exact (one_type_isofhlevel (pr111 Y) _ _ _ _).
    - intros x Hx ; simpl.
      refine (!(pathscomp0rid _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        exact (pathsinv0r (pr1 (pr211 g) x)).
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        pose (eqtohomot (pr211 α) x) as d.
        cbn in d.
        unfold homotcomp, funhomotsec, homotfun in d.
        exact d.
      }
      refine (!_).
      refine (!(pathscomp0rid _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        exact (pathsinv0r (pr1 (pr211 g) x)).
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        pose (eqtohomot (pr211 β) x) as d.
        cbn in d.
        unfold homotcomp, funhomotsec, homotfun in d.
        exact d.
      }
      refine (!_).
      apply maponpaths_2.
      do 2 apply maponpaths.
      exact (HIT_eq_property_help _ Hx).
  Qed.
End HITIsInitial.
  
Definition HIT_is_initial
           {Σ : hit_signature}
           (X : hit_algebra_one_types Σ)
  : is_HIT Σ X → is_initial Σ X.
Proof.
  intros HX.
  unfold is_initial.
  apply is_biinitial'_to_is_biinitial.
  use make_is_biinitial'.
  - exact (HIT_1cell_property X HX).
  - exact (HIT_2cell_property X HX).
  - exact (HIT_eq_property X HX).
Defined.

Definition HIT_unique
           {Σ : hit_signature}
           (X Y : hit_algebra_one_types Σ)
           (HX : is_HIT _ X)
           (HY : is_HIT _ Y)
  : X = Y.
Proof.
  apply (biinitial_unique
           _ _
           X (HIT_is_initial _ HX)
           Y (HIT_is_initial _ HY)).
Defined.
