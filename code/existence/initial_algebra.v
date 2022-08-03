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

Definition maponpaths_homotsec
           {X Y : UU}
           {f g : X →  Y}
           (e : f ~ g)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
  : maponpaths f p @ e x₂ = e x₁ @ maponpaths g p.
Proof.
  induction p.
  exact (!(pathscomp0rid _)).
Defined.

Definition initial_algebra_is_HIT
           (Σ : hit_signature)
           (X : hit_algebra_one_types Σ)
  : is_initial Σ X → is_HIT Σ X.
Proof.
  intros HX Y.
  use section_to_disp_alg_map_alt.
  - apply HX.
  - pose (is_biinitial_2cell_property
            HX
            X
            (pr1 HX (total_algebra Y) · projection Y)
            (id₁ X))
      as b.
    refine (isotoid_2_1 _ (b ,, _)).
    + apply is_univalent_2_hit_algebra_one_types.
    + apply hit_alg_is_invertible_2cell_one_type.
Defined.

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
      (poly_dmap P (λ z, f z = g z) e x)
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

  Section HIT2Cell.
    Variable (f g : X --> Y).

    Definition HIT_2cell_property_on_point
               (x : poly_act (point_constr Σ) (alg_carrier X))
               (Hx : poly_dact_UU
                       (point_constr Σ)
                       (λ z, (pr111 f) z = (pr111 g) z)
                       x)
      : (pr111 f) (alg_constr X x) = (pr111 g) (alg_constr X x)
      := pr1 (pr211 f) x
         @ maponpaths
             (pr211 Y)
             (HIT_2cell_property_help
                (point_constr Σ)
                Hx)
         @ !(pr1 (pr211 g) x).
 
    Definition poly_dact_UU_sem_endpoint
               {P Q : poly_code}
               (e : endpoint (point_constr Σ) P Q)
               (x : poly_act P (alg_carrier X))
               (Hx : poly_dact_UU
                       P
                       (λ x, (pr111 f) x = (pr111 g) x)
                       x)
      : poly_dact_UU
          Q
          (λ x, (pr111 f) x = (pr111 g) x)
          (sem_endpoint_UU e (alg_constr X) x).
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q
                      | P Q R e₁ IHe₁ e₂ IHe₂
                      | P T t | C₁ C₂ h | ].
      - exact Hx.
      - exact (IHe₂ _ (IHe₁ _ Hx)).
      - exact Hx.
      - exact Hx.
      - exact (pr1 Hx).
      - exact (pr2 Hx).
      - exact (IHe₁ _ Hx ,, IHe₂ _ Hx).
      - exact t.
      - exact (h Hx).
      - apply HIT_2cell_property_on_point.
        exact Hx.
    Defined.

    Definition HIT_2cell_property_on_path_lem
               {P Q : poly_code}
               (e : endpoint (point_constr Σ) P Q)
               (x : poly_act P (alg_carrier X))
               (Hx : poly_dact_UU
                       P
                       (λ x, (pr111 f) x = (pr111 g) x)
                       x)
      : HIT_2cell_property_help
          Q
          (endpoint_dact_UU
             (alg_constr X)
             (λ x0, (pr111 f) x0 = (pr111 g) x0)
             e
             (λ (x0 : poly_act (point_constr Σ) (alg_carrier X))
                (Hx0 : poly_dact_UU
                         (point_constr Σ)
                         (λ x1 : alg_carrier X, (pr111 f) x1 = (pr111 g) x1)
                         x0),
              (pr121 (pr1 f)) x0
              @ maponpaths (pr211 Y) (HIT_2cell_property_help (point_constr Σ) Hx0)
              @ ! (pr121 (pr1 g)) x0)
             Hx)
        =
        sem_endpoint_UU_natural
          e
          (pr121 (pr1 f))
          x
        @ maponpaths
            (sem_endpoint_UU e (pr211 Y))
            (HIT_2cell_property_help
               _
               Hx)
        @ !(sem_endpoint_UU_natural
              e
              (pr121 (pr1 g))
              x).
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q
                      | P Q R e₁ IHe₁ e₂ IHe₂
                      | P T t | C₁ C₂ h | ].
      - simpl ; unfold idfun.
        refine (!_).
        exact (pathscomp0rid _ @ maponpathsidfun _).
      - simpl.
        refine (IHe₂ _ _ @ _).
        refine (_ @ path_assoc _ _ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          apply pathscomp_inv.
        }
        do 2 refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply maponpathsinv0.
          }
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply maponpathscomp.
            }
            refine (!_).
            apply maponpathscomp0.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        exact (!(IHe₁ _ _)).
      - exact (!(pathscomp0rid _)).
      - exact (!(pathscomp0rid _)).
      - simpl.
        refine (!_).
        refine (pathscomp0rid _ @ _).
        exact (maponpaths_pr1_pathsdirprod _ _).
      - simpl.
        refine (!_).
        refine (pathscomp0rid _ @ _).
        exact (maponpaths_pr2_pathsdirprod _ _).
      - simpl.
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply pathsdirprod_inv.
            }
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths_prod_path.
            }
            apply pathsdirprod_concat.
          }
          apply pathsdirprod_concat.
        }
        refine (!_).
        exact (paths_pathsdirprod (IHe₁ _ _) (IHe₂ _ _)).
      - simpl.
        refine (_ @ !(pathscomp0rid _)).
        exact (!(maponpaths_for_constant_function _ _)).
      - apply idpath.
      - apply idpath.
    Qed.

    Definition HIT_2cell_property_on_path
               (j : path_label Σ)
               (x : poly_act (path_source Σ j) (alg_carrier X))
               (Hx : poly_dact_UU
                       (path_source Σ j)
                       (λ x, (pr111 f) x = (pr111 g) x)
                       x)
      : maponpaths (pr111 f) (alg_path X j x)
      @ endpoint_dact_UU
          (alg_constr X)
          (λ z, (pr111 f) z = (pr111 g) z)
          (path_right Σ j)
          HIT_2cell_property_on_point
          Hx
      =
      endpoint_dact_UU
        (alg_constr X)
        (λ z, (pr111 f) z = (pr111 g) z)
        (path_left Σ j)
        HIT_2cell_property_on_point Hx
      @ maponpaths (pr111 g) (alg_path X j x).
    Proof.
      etrans.
      {
        apply maponpaths.
        apply (HIT_2cell_property_on_path_lem (path_right Σ j)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (HIT_2cell_property_on_path_lem (path_left Σ j)).
      }
      simpl.
      pose (eqtohomot (pr21 f j) x) as p.
      cbn in p.
      unfold homotcomp, homotfun, funhomotsec in p.
      refine (!_).
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.        
        exact p.
      }
      clear p.
      refine (!(path_assoc _ _ _) @ _).
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply homotsec_natural'.
      }
      refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
      apply maponpaths.
      use path_inv_rotate_rl.
      refine (path_assoc _ _ _ @ _).
      use path_inv_rotate_lr.
      refine (!_).
      exact (eqtohomot (pr21 g j) x).
    Qed.
      
    Definition HIT_2cell_property_2cell
      : pr111 f ==> pr111 g.
    Proof.
      simple refine (pr1 (hit_ind_set HX _ _ _ _)).
      - exact (λ _, one_type_isofhlevel (pr111 Y) _ _).
      - exact HIT_2cell_property_on_point.
      - intros j x Hx ; simpl.
        apply map_PathOver.
        exact (HIT_2cell_property_on_path j x Hx).
    Defined.
  End HIT2Cell.

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
  use make_is_biinitial.
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
  use (biinitial_unique
         _
         (HIT_is_initial _ HY)
         (HIT_is_initial _ HX)).
  apply is_univalent_2_hit_algebra_one_types.
Defined.
