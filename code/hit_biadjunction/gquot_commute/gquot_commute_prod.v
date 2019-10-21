(** Commutation of groupoid quotient with products *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

Opaque ps_comp.

Definition prod_gquot_comp
           {P₁ P₂ : poly_code}
           {G : groupoid}
  : gquot (poly_act_groupoid P₁ G)
    → gquot (poly_act_groupoid P₂ G)
    → gquot (poly_act_groupoid (P₁ * P₂) G).
Proof.
  use gquot_double_rec'.
  - exact (gtrunc _).
  - exact (λ x y, gcl (poly_act_groupoid (P₁ * P₂) G) (x ,, y)).
  - intros x y₁ y₂ g ; simpl in *.
    refine (gcleq (poly_act_groupoid (P₁ * P₂) G) _) ; simpl.
    exact (poly_act_identity x ,, g).
  - exact (λ x y, ge (poly_act_groupoid (P₁ * P₂) G) (x ,, y)).
  - intros x y₁ y₂ y₃ g₁ g₂.
    refine (_ @ gconcat (poly_act_groupoid (P₁ * P₂) G) _ _).
    apply maponpaths.
    exact (maponpaths (λ z, z ,, _) (!(poly_act_id_left _))).
  - intros x₁ x₂ y g ; simpl in *.
    refine (gcleq (poly_act_groupoid (P₁ * P₂) G) _) ; simpl.
    exact (g ,, poly_act_identity y).
  - exact (λ x y, ge (poly_act_groupoid (P₁ * P₂) G) (x ,, y)).
  - intros x y₁ y₂ y₃ g₁ g₂.
    refine (_ @ gconcat (poly_act_groupoid (P₁ * P₂) G) _ _).
    apply maponpaths.
    exact (maponpaths (λ z, g₁ · g₂ ,, z) (!(poly_act_id_left _))).
  - intros x₁ x₂ y₁ y₂ g₁ g₂ ; simpl in *.
    refine (!(gconcat _ _ _)
             @ maponpaths (gcleq (poly_act_groupoid (P₁ * P₂) G)) _
             @ gconcat _ _ _).
    exact (pathsdirprod
             (poly_act_id_left _ @ !(poly_act_id_right _))
             (poly_act_id_right _ @ !(poly_act_id_left _))).
Defined.

(** Groupoid quotient commute with product *)
Section GQuotProd.
  Context {P₁ P₂ : poly_code}
          (IHP₁ : pstrans
                    (ps_comp (⟦ P₁ ⟧) gquot_psfunctor)
                    (ps_comp gquot_psfunctor ⦃ P₁ ⦄))
          (IHP₂ : pstrans
                    (ps_comp (⟦ P₂ ⟧) gquot_psfunctor)
                    (ps_comp gquot_psfunctor ⦃ P₂ ⦄)).
  
  Definition prod_gquot_data_comp
             (G : groupoid)
    : poly_act P₁ (gquot G) × poly_act P₂ (gquot G)
      →
      gquot (poly_act_groupoid (P₁ * P₂) G)
    := uncurry (λ x y, prod_gquot_comp (IHP₁ G x) (IHP₂ G y)).

  Definition prod_gquot_data_comp_nat_help
             (G₁ G₂ : groupoid)
             (F : G₁ ⟶ G₂)
    : ∏ (x₁ : gquot (poly_act_groupoid P₁ G₁))
        (x₂ : gquot (poly_act_groupoid P₂ G₁)),
      gquot_functor_map
        (poly_act_functor (P₁ * P₂) F)
        (prod_gquot_comp x₁ x₂) =
      prod_gquot_comp
        (gquot_functor_map (poly_act_functor P₁ F) x₁)
        (gquot_functor_map (poly_act_functor P₂ F) x₂).
  Proof.
    use gquot_double_ind_set.
    - intros a b.
      exact (gtrunc _ _ _).
    - exact (λ _ _, idpath _).
    - abstract
     (intros a b₁ b₂ g ;
      apply map_PathOver ;
      refine (whisker_square
                (idpath _)
                (!_)
                (!_)
                (idpath _)
                _) ;
      [ refine (!(maponpathscomp _ _ _) @ _) ;
        refine (maponpaths
                  (maponpaths
                     (gquot_functor_map (poly_act_functor (P₁ * P₂) F)))
                  (gquot_double_rec'_beta_r_gcleq
                     (poly_act_groupoid P₁ G₁)
                     (poly_act_groupoid P₂ G₁)
                     _ _ _ _ _ _ _ _ _ _ _ g)
                  @ _) ;
        exact (gquot_rec_beta_gcleq
                 (poly_act_groupoid (P₁ * P₂) G₁)
                 _ _ _ _ _ _ _ _ _)
      | refine (!(maponpathscomp _ _ _) @ _) ;
        refine (maponpaths
                  (maponpaths
                     (prod_gquot_comp
                        (gquot_functor_map
                           (poly_act_functor P₁ F)
                           (gcl (poly_act_groupoid P₁ G₁) a))))
                  (gquot_rec_beta_gcleq
                     (poly_act_groupoid P₂ G₁)
                     _ _ _ _ _ _ _ _ _)
                  @ _) ;
        exact (gquot_double_rec'_beta_r_gcleq
                 (poly_act_groupoid P₁ G₂)
                 (poly_act_groupoid P₂ G₂)
                   _ _ _ _ _ _ _ _ _ _ _ _)
      | refine (pathscomp0rid _ @ _) ;
        refine (maponpaths (gcleq (poly_act_groupoid (P₁ * P₂) G₂)) _) ;
        simpl ;
        refine (maponpaths (λ z, z ,, _) _) ;
        exact (pr1 (poly_act_functor_is_functor P₁ F) a)]).
    - abstract (
      intros a₁ a₂ b g;
      apply map_PathOver;
      refine (whisker_square
                (idpath _)
                (!_)
                (!_)
                (idpath _)
                _) ;
      [ refine (!(maponpathscomp
                    (λ z, prod_gquot_comp z (gcl (poly_act_groupoid P₂ G₁) b))
                    (gquot_functor_map (poly_act_functor (P₁ * P₂) F)) _) @ _);
        refine (maponpaths
                  (maponpaths (gquot_functor_map (poly_act_functor (P₁ * P₂) F)))
                  (gquot_double_rec'_beta_l_gcleq
                     (poly_act_groupoid P₁ G₁)
                     (poly_act_groupoid P₂ G₁)
                     _ _ _ _ _ _ _ _ _ _ _ g)
                  @ _);
        exact (gquot_rec_beta_gcleq
                 (poly_act_groupoid (P₁ * P₂) G₁)
                 _ _ _ _ _ _ _ _ _)
      | refine (!(maponpathscomp
                    (gquot_functor_map (poly_act_functor P₁ F))
                    (λ z, prod_gquot_comp z _)
                    _) @ _);
        refine (maponpaths
                  (maponpaths
                     (λ z,
                      prod_gquot_comp
                        z
                        (gquot_functor_map
                           (poly_act_functor P₂ F)
                           (gcl (poly_act_groupoid P₂ G₁) b))))
                  (gquot_rec_beta_gcleq
                     (poly_act_groupoid P₁ G₁)
                     _ _ _ _ _ _ _ _ _)
                  @ _);
        exact (gquot_double_rec'_beta_l_gcleq
                 (poly_act_groupoid P₁ G₂)
                 (poly_act_groupoid P₂ G₂)
                 _ _ _ _ _ _ _ _ _ _ _ _)
      | refine (pathscomp0rid _ @ _);
        refine (maponpaths (gcleq (poly_act_groupoid (P₁ * P₂) G₂)) _);
        simpl;
        refine (maponpaths (λ z, _ ,, z) _);
        exact (pr1 (poly_act_functor_is_functor P₂ F) b)]).
  Defined.

  Local Definition IHP₁_help
        {G₁ G₂ : groupoid}
        (F : G₁ ⟶ G₂)
    : ∏ (x : poly_act P₁ (gquot G₁)),
      gquot_functor_map (poly_act_functor P₁ F) (IHP₁ G₁ x)
      =
      IHP₁ G₂ (poly_map P₁ (gquot_functor_map F) x)
    := pr1 (psnaturality_of IHP₁ F).

  Local Definition IHP₂_help
        {G₁ G₂ : groupoid}
        (F : G₁ ⟶ G₂)
    : ∏ (x : poly_act P₂ (gquot G₁)),
      gquot_functor_map (poly_act_functor P₂ F) (IHP₂ G₁ x)
      =
      IHP₂ G₂ (poly_map P₂ (gquot_functor_map F) x)
    := pr1 (psnaturality_of IHP₂ F).

  Local Definition IHP₁_help_nat
        {G₁ G₂ : groupoid}
        {F₁ F₂ : G₁ ⟶ G₂}
        (p : nat_trans F₁ F₂)
        (x : poly_act P₁ (gquot G₁))
    : gquot_functor_cell
        (poly_act_nat_trans P₁ p) (IHP₁ G₁ x)
      @ IHP₁_help F₂ x
      =
      IHP₁_help F₁ x
      @ maponpaths (IHP₁ G₂) (poly_homot P₁ (gquot_functor_cell p) x).
  Proof.
    exact (eqtohomot (psnaturality_natural IHP₁ _ _ _ _ p) x).
  Qed.

  Local Definition IHP₂_help_nat
        {G₁ G₂ : groupoid}
        {F₁ F₂ : G₁ ⟶ G₂}
        (p : nat_trans F₁ F₂)
        (x : poly_act P₂ (gquot G₁))
    : gquot_functor_cell
        (poly_act_nat_trans P₂ p) (IHP₂ G₁ x)
      @ IHP₂_help F₂ x
      =
      IHP₂_help F₁ x
      @ maponpaths (IHP₂ G₂) (poly_homot P₂ (gquot_functor_cell p) x).
  Proof.
    exact (eqtohomot (psnaturality_natural IHP₂ _ _ _ _ p) x).
  Qed.
  
  Definition prod_gquot_data_comp_nat
             (G₁ G₂ : groupoid)
             (F : G₁ ⟶ G₂)
    : (λ x, gquot_functor_map
              (poly_act_functor (P₁ * P₂) F)
              (prod_gquot_data_comp G₁ x))
       ~
       λ x, prod_gquot_data_comp
              G₂
              (dirprodf
                 (poly_map P₁ (gquot_functor_map F))
                 (poly_map P₂ (gquot_functor_map F))
                 x).
  Proof.
    intro x.
    refine (prod_gquot_data_comp_nat_help
              G₁ G₂ F
              (IHP₁ G₁ (pr1 x)) (IHP₂ G₁ (pr2 x)) @ _).
    refine (maponpaths
             (λ z, prod_gquot_comp z _)
             (IHP₁_help F (pr1 x))
             @ _).
    exact (maponpaths
             (prod_gquot_comp _)
             (IHP₂_help F (pr2 x))).
  Defined.

  Definition prod_gquot_data
    : pstrans_data
        (ps_comp (⟦ P₁ * P₂ ⟧) gquot_psfunctor)
        (ps_comp gquot_psfunctor ⦃ P₁ * P₂ ⦄).
  Proof.
    use make_pstrans_data.
    - exact prod_gquot_data_comp.
    - intros G₁ G₂ F.
      use make_invertible_2cell.
      + exact (prod_gquot_data_comp_nat G₁ G₂ F).
      + apply one_type_2cell_iso.
  Defined.

  (** To show it is a pseudonatural trasfomation, we use the following lemmata *)

  (** For: naturality 2-cell is natural *)
  Definition maponpaths_prod_gquot_data_comp
             {G : groupoid}
             {x₁ x₂ : poly_act P₁ (gquot G) × poly_act P₂ (gquot G)}
             (p : x₁ = x₂)
    : maponpaths
        (prod_gquot_data_comp G)
        p
      =
      maponpaths
        (λ (x : gquot (poly_act_groupoid P₁ G)
                      × gquot (poly_act_groupoid P₂ G)),
         prod_gquot_comp (pr1 x) (pr2 x))
        (pathsdirprod
           (maponpaths (λ z, IHP₁ G z) (maponpaths pr1 p))
           (maponpaths (λ z, IHP₂ G z) (maponpaths dirprod_pr2 p))).
  Proof.
    induction p.
    apply idpath.
  Defined.

  (** First condition *)  
  Definition prod_gquot_is_pstrans_nat_lem
             {X Y : grpd_bicat}
             {f g : grpd_bicat ⟦ X, Y ⟧}
             (p : f ==> g)
    : ∏ (z₁ : gquot (poly_act_groupoid P₁ X)) (z₂ : gquot (poly_act_groupoid P₂ X)),
      prod_gquot_data_comp_nat_help X Y f z₁ z₂
    @ maponpaths
        (λ z : gquot (poly_act_groupoid P₁ Y) × gquot (poly_act_groupoid P₂ Y),
               prod_gquot_comp (pr1 z) (pr2 z))
        (pathsdirprod
           (gquot_functor_cell
              (poly_act_nat_trans P₁ p) z₁)
           (gquot_functor_cell
              (poly_act_nat_trans P₂ p) z₂))
    =
    gquot_functor_cell
      (poly_act_nat_trans (P₁ * P₂) p)
      (prod_gquot_comp z₁ z₂)
    @ prod_gquot_data_comp_nat_help X Y g z₁ z₂.
  Proof.
    use gquot_double_ind_prop.
    - intros a b.
      exact (gtrunc _ _ _ _ _).
    - intros a b.
      refine (pathscomp0lid _ @ _ @ !(pathscomp0rid _)).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          simpl.
          apply idpath.
        }
        refine (uncurry_ap
                (λ (x : gquot (poly_act_groupoid P₁ Y))
                   (y : gquot (poly_act_groupoid P₂ Y)),
                 prod_gquot_comp x y)
                (gcleq
                   (poly_act_groupoid P₁ Y)
                   (poly_act_nat_trans_data P₁ p a))
                (gcleq
                   (poly_act_groupoid P₂ Y)
                   (poly_act_nat_trans_data P₂ p b)) @ _).
        etrans.
        {
          apply maponpaths.
          exact (gquot_double_rec'_beta_r_gcleq
                   (poly_act_groupoid P₁ Y)
                   (poly_act_groupoid P₂ Y)
                   _ _ _ _ _ _ _ _ _ _ _ _).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (gquot_double_rec'_beta_l_gcleq
                   (poly_act_groupoid P₁ Y)
                   (poly_act_groupoid P₂ Y)
                   _ _ _ _ _ _ _ _ _ _ _ _).
        }
        refine (!_).
        exact (gconcat (poly_act_groupoid (P₁ * P₂) Y) _ _).
      }
      refine (maponpaths (gcleq (poly_act_groupoid (P₁ * P₂) Y)) _).
      use pathsdirprod.
      + apply poly_act_id_right.
      + apply poly_act_id_left.
  Qed.
  
  Definition prod_gquot_is_pstrans_lem₁
             (X Y : grpd_bicat)
             (f g : grpd_bicat ⟦ X, Y ⟧)
             (p : f ==> g)
             (x : poly_act P₁ (gquot X) × poly_act P₂ (gquot X))
    : (prod_gquot_data_comp_nat X Y f x)
        @ maponpaths
            (prod_gquot_data_comp Y)
            (## (⟦ P₁ * P₂ ⟧) (## gquot_psfunctor p) x)
      =
      gquot_functor_cell
        (poly_act_nat_trans (P₁ * P₂) p) (prod_gquot_data_comp X x)
      @ prod_gquot_data_comp_nat X Y g x.
  Proof.
    unfold prod_gquot_data_comp_nat.
    unfold prod_gquot_data_comp_nat_help.
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        pose (uncurry_ap
                (λ (x : gquot (poly_act_groupoid P₁ Y))
                   (y : gquot (poly_act_groupoid P₂ Y)),
                 prod_gquot_comp x y)
                (IHP₁_help f (pr1 x))
                (IHP₂_help f (pr2 x))) as r.
        unfold uncurry in r.
        exact r.
      }
      etrans.
      {
        apply maponpaths.
        exact (maponpaths_prod_gquot_data_comp (## (⟦ P₁ * P₂ ⟧) (## gquot_psfunctor p) x)).
      }
      etrans.
      {
        refine (!_).
        exact (maponpathscomp0
                 (λ z : gquot (poly_act_groupoid P₁ Y) × gquot (poly_act_groupoid P₂ Y),
                        prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (IHP₁_help f (pr1 x))
                    (IHP₂_help f (pr2 x)))
                 (pathsdirprod
                    (maponpaths
                       (IHP₁ Y)
                       (maponpaths
                          pr1
                          (## (⟦ P₁ * P₂ ⟧) (## gquot_psfunctor p) x)))
                    (maponpaths
                       (IHP₂ Y)
                       (maponpaths
                          dirprod_pr2
                          (## (⟦ P₁ * P₂ ⟧) (## gquot_psfunctor p) x))))).
      }
      apply maponpaths.
      etrans.
      {
        apply pathsdirprod_concat.
      }
      etrans.
      {
        refine (maponpaths (λ z, pathsdirprod (_ @ maponpaths (IHP₁ Y) z) _) _).
        apply maponpaths_pr1_pathsdirprod.
      }
      etrans.
      {
        refine (maponpaths (λ z, pathsdirprod _ (_ @ maponpaths (IHP₂ Y) z)) _).
        apply maponpaths_pr2_pathsdirprod.
      }
      etrans.
      {
        refine (maponpaths (λ z, pathsdirprod z _) _).
        exact (!(IHP₁_help_nat p (pr1 x))).
      }
      etrans.
      {
        refine (maponpaths (λ z, pathsdirprod _ z) _).
        exact (!(IHP₂_help_nat p (pr2 x))).
      }
      refine (!_).
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply maponpaths.
      refine (maponpathscomp0
               (λ z : gquot (poly_act_groupoid P₁ Y) × gquot (poly_act_groupoid P₂ Y),
                      prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod
                  (gquot_functor_cell
                     (poly_act_nat_trans P₁ p) (IHP₁ X (pr1 x)))
                  (gquot_functor_cell
                     (poly_act_nat_trans P₂ p) (IHP₂ X (pr2 x))))
               (pathsdirprod
                  (IHP₁_help g (pr1 x))
                  (IHP₂_help g (pr2 x)))
               @ _).
      apply maponpaths.
      pose (uncurry_ap
              (λ (x : gquot (poly_act_groupoid P₁ Y))
                 (y : gquot (poly_act_groupoid P₂ Y)),
               prod_gquot_comp x y)
              (IHP₁_help g (pr1 x))
              (IHP₂_help g (pr2 x))) as r.
        unfold uncurry in r.
        exact r.
    }
    refine (path_assoc _ _ _ @ _).
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    exact (prod_gquot_is_pstrans_nat_lem p (IHP₁ X (pr1 x)) (IHP₂ X (pr2 x))).
  Qed.

  (** Second condition *)
  Definition prod_gquot_is_pstrans_lem₂_help
             (G : grpd_bicat)
    : ∏ (z₁ : gquot (poly_act_groupoid P₁ G))
        (z₂ : gquot (poly_act_groupoid P₂ G)),
      gquot_functor_identity
        (poly_act_groupoid (P₁ * P₂) G) (prod_gquot_comp z₁ z₂)
    @ gquot_functor_cell
        (poly_act_functor_identity (P₁ * P₂) G)
        (prod_gquot_comp z₁ z₂)
    @ prod_gquot_data_comp_nat_help
        G G (functor_identity _) z₁ z₂
    =
    maponpaths
      (λ z, prod_gquot_comp (pr1 z) (pr2 z))
      (pathsdirprod
         ((pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₁ ⦄))) G z₁)
         ((pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₂ ⦄))) G z₂)).
  Proof.
    use gquot_double_ind_prop.
    - intros a b.
      exact (gtrunc _ _ _ _ _).
    - intros a b.
      etrans.
      {
        apply maponpaths.
        apply pathscomp0rid.
      }
      etrans.
      {
        apply pathscomp0lid.
      }
      refine (!_).
      etrans.
      {
        pose (uncurry_ap
                prod_gquot_comp
                (gcleq (poly_act_groupoid P₁ G) (poly_act_functor_identity_data P₁ G a))
                (gcleq (poly_act_groupoid P₂ G) (poly_act_functor_identity_data P₂ G b)))
          as r.
        unfold uncurry in r.
        exact r.
      }
      etrans.
      {
        refine (maponpaths (λ z, _ @ z) _).
        exact (gquot_double_rec'_beta_r_gcleq
                 (poly_act_groupoid P₁ G)
                 (poly_act_groupoid P₂ G)
                 _ _ _ _ _ _ _ _ _ _ _ _).
      }
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (gquot_double_rec'_beta_l_gcleq
                 (poly_act_groupoid P₁ G)
                 (poly_act_groupoid P₂ G)
                 _ _ _ _ _ _ _ _ _ _ _ _).
      }
      refine (!(gconcat (poly_act_groupoid (P₁ * P₂) G) _ _) @ _).
      refine (maponpaths (gcleq (poly_act_groupoid (P₁ * P₂) G)) _).
      apply pathsdirprod.
      + apply poly_act_id_right.
      + apply poly_act_id_left.
  Qed.

  Definition prod_gquot_is_pstrans_lem₂
             {G : grpd_bicat}
             (x : poly_act P₁ (gquot G) × poly_act P₂ (gquot G))
    : (gquot_functor_identity
         (poly_act_groupoid (P₁ * P₂) G)
         (prod_gquot_data_comp G x)
     @ gquot_functor_cell
        (poly_act_functor_identity (P₁ * P₂) G)
        (prod_gquot_data_comp G x))
    @ prod_gquot_data_comp_nat G G (functor_identity _) x
     =
     maponpaths
       (prod_gquot_data_comp G)
       (dirprodf_path
          (poly_id P₁ (gquot G)) (poly_id P₂ (gquot G)) x
            @ poly_homot (P₁ * P₂)
          (gquot_functor_identity G) x).
  Proof.
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths_prod_gquot_data_comp.
      }
      apply maponpaths.
      etrans.
      {
        refine (maponpaths (λ z, pathsdirprod z _) _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (pathsdirprod_concat
                     (poly_id P₁ (gquot G) (pr1 x))
                     (poly_homot P₁ (gquot_functor_identity G) (pr1 x))
                     (poly_id P₂ (gquot G) (pr2 x))
                     (poly_homot P₂ (gquot_functor_identity G) (pr2 x))).
          }
          apply maponpaths_pr1_pathsdirprod.
        }
        exact (!(eqtohomot (pstrans_id IHP₁ G) (pr1 x))
               : _
               = (pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₁ ⦄))) G (IHP₁ G (pr1 x))
               @ IHP₁_help (functor_identity _) (pr1 x)).
      }
      etrans.
      {
        refine (maponpaths (pathsdirprod _) _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (pathsdirprod_concat
                     (poly_id P₁ (gquot G) (pr1 x))
                     (poly_homot P₁ (gquot_functor_identity G) (pr1 x))
                     (poly_id P₂ (gquot G) (pr2 x))
                     (poly_homot P₂ (gquot_functor_identity G) (pr2 x))).
          }
          apply maponpaths_pr2_pathsdirprod.
        }
        exact (!(eqtohomot (pstrans_id IHP₂ G) (pr2 x))
               : _
               = (pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₂ ⦄))) G (IHP₂ G (pr2 x))
               @ IHP₂_help (functor_identity _) (pr2 x)).
      }
      refine (!_).
      apply pathsdirprod_concat.
    }      
    unfold prod_gquot_data_comp_nat.
    etrans.
    {
      apply (maponpathscomp0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    ((pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₁ ⦄))) G (IHP₁ G (pr1 x)))
                    ((pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₂ ⦄))) G (IHP₂ G (pr2 x))))
                 (pathsdirprod
                    (IHP₁_help (functor_identity _) (pr1 x))
                    (IHP₂_help (functor_identity _) (pr2 x)))
            ).
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      pose (uncurry_ap
              (λ (x : gquot (poly_act_groupoid P₁ _))
                 (y : gquot (poly_act_groupoid P₂ _)),
               prod_gquot_comp x y)
              (IHP₁_help (functor_identity _) (pr1 x))
              (IHP₂_help (functor_identity _) (pr2 x))) as r.
      unfold uncurry in r.
      exact (!r).
    }
    refine ((path_assoc _ _ _) @ _).
    refine (maponpaths (λ z, z @ _) _).
    refine (!(path_assoc _ _ _) @ _).
    exact (prod_gquot_is_pstrans_lem₂_help G (IHP₁ G (pr1 x)) (IHP₂ G (pr2 x))).
  Qed.

  (** Third condition *)
  Definition prod_gquot_is_pstrans_lem₃_help₁
             {Y Z : grpd_bicat}
             (g : grpd_bicat ⟦ Y, Z ⟧)
             {z₁ z₁' : gquot (poly_act_groupoid P₁ Y)}
             {z₂ z₂' : gquot (poly_act_groupoid P₂ Y)}
             (p : z₁ = z₁')
             (q : z₂ = z₂')
    : maponpaths
        (gquot_functor_map (poly_act_functor (P₁ * P₂) g))
        (maponpaths
           (λ z,
            prod_gquot_comp (pr1 z) (pr2 z))
           (pathsdirprod p q))
    @ prod_gquot_data_comp_nat_help Y Z g z₁' z₂'
    =
    prod_gquot_data_comp_nat_help
      Y Z g z₁ z₂
    @ maponpaths
        (λ z, prod_gquot_comp (pr1 z) (pr2 z))
        (pathsdirprod
           (maponpaths (gquot_functor_map (poly_act_functor P₁ g)) p)
           (maponpaths (gquot_functor_map (poly_act_functor P₂ g)) q)).
  Proof.
    induction p.
    induction q.
    exact (pathscomp0lid _ @ !(pathscomp0rid _)).
  Qed.

  Local Definition IHP₁_comp_help
        {X Y Z : grpd_bicat}
        (f : grpd_bicat ⟦ X, Y ⟧)
        (g : grpd_bicat ⟦ Y, Z ⟧)
        (x : poly_act P₁ (gquot X) × poly_act P₂ (gquot X))
    : (gquot_functor_composition
         (poly_act_functor P₁ f) (poly_act_functor P₁ g)
         (IHP₁ X (pr1 x))
    @ gquot_functor_cell
        (poly_act_functor_composition P₁ f g)
        (IHP₁ X (pr1 x)))
    @ IHP₁_help (f ∙ g) (pr1 x)
    = (maponpaths
         (gquot_functor_map (poly_act_functor P₁ g))
         (IHP₁_help f (pr1 x))
    @ IHP₁_help g (poly_map P₁ (gquot_functor_map f) (pr1 x)))
    @ maponpaths
        (IHP₁ Z)
        (poly_comp P₁ (gquot_functor_map f) (gquot_functor_map g) (pr1 x)
    @ poly_homot P₁ (gquot_functor_composition f g) (pr1 x)).
  Proof.
    refine (eqtohomot (pstrans_comp IHP₁ f g) (pr1 x) @ _).
    refine (maponpaths
             (λ z, z @ _)
             (pathscomp0rid _ @ (maponpaths (λ z, z @ _) (pathscomp0rid _)) @ _)).
    apply idpath.
  Qed.
  
  Local Definition IHP₂_comp_help
        {X Y Z : grpd_bicat}
        (f : grpd_bicat ⟦ X, Y ⟧)
        (g : grpd_bicat ⟦ Y, Z ⟧)
        (x : poly_act P₁ (gquot X) × poly_act P₂ (gquot X))
    : (gquot_functor_composition
         (poly_act_functor P₂ f) (poly_act_functor P₂ g)
         (IHP₂ X (pr2 x))
    @ gquot_functor_cell
        (poly_act_functor_composition P₂ f g)
        (IHP₂ X (pr2 x)))
    @ IHP₂_help (f ∙ g) (pr2 x)
    = (maponpaths
         (gquot_functor_map (poly_act_functor P₂ g))
         (IHP₂_help f (pr2 x))
    @ IHP₂_help g (poly_map P₂ (gquot_functor_map f) (pr2 x)))
    @ maponpaths
        (IHP₂ Z)
        (poly_comp P₂ (gquot_functor_map f) (gquot_functor_map g) (pr2 x)
    @ poly_homot P₂ (gquot_functor_composition f g) (pr2 x)).
  Proof.
    refine (eqtohomot (pstrans_comp IHP₂ f g) (pr2 x) @ _).
    refine (maponpaths
             (λ z, z @ _)
             (pathscomp0rid _ @ (maponpaths (λ z, z @ _) (pathscomp0rid _)) @ _)).
    apply idpath.
  Qed.
  
  Definition prod_gquot_is_pstrans_lem₃_help₂
             {X Y Z : grpd_bicat}
             (f : grpd_bicat ⟦ X, Y ⟧)
             (g : grpd_bicat ⟦ Y, Z ⟧)
    : ∏ (z₁ : gquot (poly_act_groupoid P₁ X))
        (z₂ : gquot (poly_act_groupoid P₂ X)),
    (maponpaths
         (gquot_functor_map (poly_act_functor (P₁ * P₂) g))
         (prod_gquot_data_comp_nat_help X Y f z₁ z₂)
    @ prod_gquot_data_comp_nat_help
        Y Z g
        (gquot_functor_map (poly_act_functor P₁ f) z₁)
        (gquot_functor_map (poly_act_functor P₂ f) z₂))
    @ maponpaths
        (λ z : gquot (poly_act_groupoid P₁ Z) × gquot (poly_act_groupoid P₂ Z),
               prod_gquot_comp (pr1 z) (pr2 z))
        (pathsdirprod
           (gquot_functor_composition
              (poly_act_functor P₁ f) (poly_act_functor P₁ g)
              z₁
     @ gquot_functor_cell
         (poly_act_functor_composition P₁ f g) z₁)
           (gquot_functor_composition
              (poly_act_functor P₂ f) (poly_act_functor P₂ g)
              z₂
     @ gquot_functor_cell
         (poly_act_functor_composition P₂ f g) z₂))
     =
     (gquot_functor_composition
        (poly_act_functor (P₁ * P₂) f)
        (poly_act_functor (P₁ * P₂) g) (prod_gquot_comp z₁ z₂)
     @ gquot_functor_cell
         (poly_act_functor_composition (P₁ * P₂) f g)
         (prod_gquot_comp z₁ z₂))
     @ prod_gquot_data_comp_nat_help
         X Z (f ∙ g) z₁ z₂.
  Proof.
    use gquot_double_ind_prop.
    - intros a b.
      exact (gtrunc _ _ _ _ _).
    - intros a b.
      refine (_ @ !(pathscomp0rid _)).
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp0rid.
      }
      refine (pathscomp0lid _ @ _).
      refine (_ @ !(pathscomp0lid (gcleq _ _))).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          refine (maponpaths (λ z, pathsdirprod z _) _).
          exact (pathscomp0lid (gcleq _ _)).
        }
        refine (maponpaths (pathsdirprod _) _).
        exact (pathscomp0lid (gcleq _ _)).
      }
      etrans.
      {
        pose (uncurry_ap
                 prod_gquot_comp
                 (gcleq
                    (poly_act_groupoid P₁ Z)
                    ((poly_act_functor_composition P₁ f g) a))
                 (gcleq
                    (poly_act_groupoid P₂ Z)
                    ((poly_act_functor_composition P₂ f g) b)))
          as r.
        unfold uncurry in r.
        exact r.
      }
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (gquot_double_rec'_beta_l_gcleq
                 (poly_act_groupoid P₁ _)
                 (poly_act_groupoid P₂ _)
                 _ _ _ _ _ _ _ _ _ _ _ _).
      }
      etrans.
      {
        apply maponpaths.
        exact (gquot_double_rec'_beta_r_gcleq
                 (poly_act_groupoid P₁ _)
                 (poly_act_groupoid P₂ _)
                 _ _ _ _ _ _ _ _ _ _ _ _).
      }
      refine (!(gconcat _ _ _) @ _).
      apply maponpaths.
      apply pathsdirprod.
      + apply poly_act_id_right.
      + apply poly_act_id_left.
  Qed.
  
  Definition prod_gquot_is_pstrans_lem₃
             {X Y Z : grpd_bicat}
             (f : grpd_bicat ⟦ X, Y ⟧)
             (g : grpd_bicat ⟦ Y, Z ⟧)
             (x : poly_act P₁ (gquot X) × poly_act P₂ (gquot X))
    : (((maponpaths
            (gquot_functor_map (poly_act_functor (P₁ * P₂) g))
            (prod_gquot_data_comp_nat X Y f x)
        @ idpath _)
        @ prod_gquot_data_comp_nat
            Y Z g
            (dirprodf
               (poly_map P₁ (gquot_functor_map f))
               (poly_map P₂ (gquot_functor_map f)) x))
        @ idpath _)
        @ maponpaths
            (prod_gquot_data_comp Z)
            (dirprodf_path
               (poly_comp P₁ (gquot_functor_map f) (gquot_functor_map g))
               (poly_comp P₂ (gquot_functor_map f) (gquot_functor_map g))
               x
             @ poly_homot (P₁ * P₂) (gquot_functor_composition f g) x)
        = (gquot_functor_composition
            (poly_act_functor (P₁ * P₂) f)
            (poly_act_functor (P₁ * P₂) g)
            (prod_gquot_data_comp X x)
        @ gquot_functor_cell
            (poly_act_functor_composition (P₁ * P₂) f g)
            (prod_gquot_data_comp X x))
        @ prod_gquot_data_comp_nat X Z (f ∙ g) x.
  Proof.
    refine (maponpaths
              (λ z, z @ _)
              (pathscomp0rid _ @ (maponpaths (λ z, z @ _) (pathscomp0rid _)))
              @ _).
    etrans.
    {
      refine (maponpaths (λ z, _ @ maponpaths _ z) _).
      exact (pathsdirprod_concat
               (poly_comp P₁ (gquot_functor_map f) (gquot_functor_map g) (pr1 x))
               (poly_homot P₁ (gquot_functor_composition f g) (pr1 x))
               (poly_comp P₂ (gquot_functor_map f) (gquot_functor_map g) (pr2 x))
               (poly_homot P₂ (gquot_functor_composition f g) (pr2 x))).
    }
    etrans.
    {
      refine (maponpaths (λ z, _ @ z) _).
      apply maponpaths_prod_gquot_data_comp.
    }
    etrans.
    {
      refine (maponpaths (λ z, (_ @ z) @ _) _).
      refine (maponpaths (λ z, _ @ z) _).
      pose (uncurry_ap
              prod_gquot_comp
              (IHP₁_help g (poly_map P₁ (gquot_functor_map f) (pr1 x)))
              (IHP₂_help g (poly_map P₂ (gquot_functor_map f) (pr2 x))))
        as r.
      unfold uncurry in r.
      exact (!r).
    }
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      refine (maponpaths (λ z, _ @ z) _).
      refine (!(path_assoc _ _ _) @ _).
      refine (maponpaths (λ z, _ @ z) _).
      exact (!(maponpathscomp0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod _ _)
                 (pathsdirprod _ _)
            )).
    }
    etrans.
    {
      refine (maponpaths (λ z, _ @ (_ @ z)) _).
      apply maponpaths.
      apply maponpaths.
      etrans.
      {
        refine (maponpaths (λ z, pathsdirprod z _) _).
        apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
      }
      refine (maponpaths (pathsdirprod _) _).
      apply maponpaths.
      apply maponpaths_pr2_pathsdirprod.
    }
    etrans.
    {
      refine (maponpaths (λ z, _ @ (_ @ z)) _).
      apply maponpaths.
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply maponpaths_2.
      unfold prod_gquot_data_comp_nat.
      refine (maponpathscomp0 _ _ _ @ _).
      do 2 apply maponpaths.
      pose (uncurry_ap
               prod_gquot_comp
               (IHP₁_help f (pr1 x))
               (IHP₂_help f (pr2 x)))
        as r.
      unfold uncurry in r.
      exact (!r).
    }
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      exact (prod_gquot_is_pstrans_lem₃_help₁
               g
               (IHP₁_help f (pr1 x)) (IHP₂_help f (pr2 x))).
    }
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        exact (!(maponpathscomp0
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod _ _)
                   (pathsdirprod _ _)
              )).
      }
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_concat.
      }
      apply maponpaths.
      etrans.
      {
        refine (maponpaths (λ z, pathsdirprod z _) _).
        refine (path_assoc _ _ _ @ _).
        exact (!(IHP₁_comp_help f g x)).
      }
      refine (maponpaths (pathsdirprod _) _).
      refine (path_assoc _ _ _ @ _).
      exact (!(IHP₂_comp_help f g x)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply pathsdirprod_concat.
      }
      exact (maponpathscomp0
               (λ z : gquot (poly_act_groupoid P₁ Z) × gquot (poly_act_groupoid P₂ Z),
                      prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod _ _)
               (pathsdirprod _ _)).
    }    
    refine (!_).
    etrans.
    {
      apply maponpaths.
      unfold prod_gquot_data_comp_nat.
      apply maponpaths.
      pose (uncurry_ap
              prod_gquot_comp
              (IHP₁_help (f ∙ g) (pr1 x))
              (IHP₂_help (f ∙ g) (pr2 x)))
        as r.
      unfold uncurry in r.
      exact (!r).
    }
    refine (path_assoc _ _ _ @ _).
    refine (_ @ !(path_assoc _ _ _)).
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    exact (!(prod_gquot_is_pstrans_lem₃_help₂ f g (IHP₁ X (pr1 x)) (IHP₂ X (pr2 x)))).
  Qed.
  
  Definition prod_gquot_is_pstrans
    : is_pstrans prod_gquot_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      intro x.
      exact (!(prod_gquot_is_pstrans_lem₁ X Y f g p x)).
    - intros X.
      use funextsec.
      exact prod_gquot_is_pstrans_lem₂.
    - intros X Y Z f g.
      use funextsec.
      intro x.
      exact (!(prod_gquot_is_pstrans_lem₃ f g x)).
  Qed.
  
  Definition prod_gquot
    : pstrans
        (ps_comp (⟦ P₁ * P₂ ⟧) gquot_psfunctor)
        (ps_comp gquot_psfunctor ⦃ P₁ * P₂ ⦄).
  Proof.
    use make_pstrans.
    - exact prod_gquot_data.
    - exact prod_gquot_is_pstrans.
  Defined.
End GQuotProd.
