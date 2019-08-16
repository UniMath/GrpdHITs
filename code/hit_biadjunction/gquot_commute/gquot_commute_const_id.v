(** Commutation of groupoid quotient with constant and identity *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

Opaque ps_comp.

Definition gquot_path_groupoid
           (A : one_type)
           (X : groupoid)
  : gquot (poly_act_groupoid (C A) X) → A.
Proof.
  use gquot_rec.
  - exact (λ z, z).
  - exact (λ _ _ z, z).
  - exact (λ _, idpath _).
  - exact (λ _ _ _ _ _, idpath _).
  - apply A.
Defined.

Definition gquot_path_groupoid_identity
           (A : one_type)
           (X Y : groupoid)
           (f : X ⟶ Y)
  : ∏ (z : gquot (poly_act_groupoid (C A) X)),
    gquot_path_groupoid A X z
    =
    gquot_path_groupoid A Y (gquot_functor_map (poly_act_functor (C A) X Y f) z).
Proof.
  use gquot_ind_set.
  - exact idpath.
  - abstract
      (intros a₁ a₂ g ; cbn ;
       apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 (!((!(maponpathscomp _ (gquot_path_groupoid A Y) (gcleq _ g)))
                      @ maponpaths
                      (maponpaths (gquot_path_groupoid A Y))
                      (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                      @ gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 (idpath _)
                 _) ;
       apply vrefl).
  - intro.
    exact (one_type_isofhlevel A _ _).
Defined.

(** Commutation of groupoid quotient with constant *)
Section GQuotConstant.
  Variable (A : one_types).
  
  Definition gquot_const_data
    : pstrans_data
        (ps_comp (⟦ C A ⟧) gquot_psfunctor)
        (ps_comp gquot_psfunctor ⦃ C A ⦄).
  Proof.
    use make_pstrans_data.
    - exact (λ _, gcl (poly_act_groupoid (C A) _)).
    - intros X Y f.
      use make_invertible_2cell.
      + intro z ; apply idpath.
      + apply one_type_2cell_iso.
  Defined.

  Definition gquot_const_is_pstrans
    : is_pstrans gquot_const_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      intros z.
      exact (pathscomp0rid _ @ ge _ _).
    - intros.
      use funextsec.
      intros z.
      exact (pathscomp0rid _ @ ge _ _).
    - intros.
      use funextsec.
      intros z.
      exact (pathscomp0rid _ @ ge (poly_act_groupoid (C A) Z) z).
  Qed.

  Definition gquot_const
    : pstrans
        (ps_comp (⟦ C A ⟧) gquot_psfunctor)
        (ps_comp gquot_psfunctor ⦃ C A ⦄).
  Proof.
    use make_pstrans.
    - exact gquot_const_data.
    - exact gquot_const_is_pstrans.
  Defined.
End GQuotConstant.

(** Commutation of path groupoid with identity *)
Definition gquot_poly_act_I
           (G : groupoid)
  : gquot G → gquot (poly_act_groupoid I G).
Proof.
  use gquot_rec.
  - exact (λ x, gcl (poly_act_groupoid I G) x).
  - exact (λ x y f, gcleq (poly_act_groupoid I G) f).
  - exact (λ x, ge (poly_act_groupoid I G) x).
  - exact (λ _ _ _ g₁ g₂, gconcat (poly_act_groupoid I G) g₁ g₂).
  - exact (gtrunc (poly_act_groupoid I G)).
Defined.

Definition gquot_poly_act_I_nat
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : ∏ (x : gquot G₁),
    gquot_functor_map (poly_act_functor I G₁ G₂ F) (gquot_poly_act_I G₁ x)
    =
    gquot_poly_act_I G₂ (gquot_functor_map F x).
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract (refine (λ a₁ a₂ g, _) ; simpl ;
    apply map_PathOver ;
    refine (whisker_square
              (idpath _)
              _
              _
              (idpath _)
              _) ;
      [ refine (!((!(maponpathscomp _ _ _))
                    @ maponpaths
                        (maponpaths (gquot_functor_map (poly_act_functor I G₁ G₂ F)))
                        (gquot_rec_beta_gcleq G₁ _ _ _ _ _ _ _ _ g)
                    @ _)) ;
      exact (gquot_rec_beta_gcleq (poly_act_groupoid I G₁) _ _ _ _ _ _ _ _ _)
      | refine (!(!(maponpathscomp _ _ _)
                     @ maponpaths
                         (maponpaths (gquot_poly_act_I G₂))
                         (gquot_rec_beta_gcleq G₁ _ _ _ _ _ _ _ _ g)
                     @ _)) ;
      exact (gquot_rec_beta_gcleq G₂ _ _ _ _ _ _ _ _ (#F g))
      | exact (vrefl (gcleq (poly_act_groupoid I G₂) (# F g))) ]).
  - exact (λ _, gtrunc _ _ _).
Defined.

Definition id_gquot_data
  : pstrans_data
      (ps_comp (⟦ I ⟧) gquot_psfunctor)
      (ps_comp gquot_psfunctor ⦃ I ⦄).
Proof.
  use make_pstrans_data.
  - exact gquot_poly_act_I.
  - intros G₁ G₂ F.
    use make_invertible_2cell.
    + exact (gquot_poly_act_I_nat G₁ G₂ F).
    + apply one_type_2cell_iso.
Defined.

Definition id_gquot_is_pstrans
  : is_pstrans id_gquot_data.
Proof.
  repeat split.
  - intros X Y f g p.
    use funextsec.
    use gquot_ind_prop.
    + intros a.
      exact (pathscomp0rid _ @ !(gquot_rec_beta_gcleq Y _ _ _ _ _ _ _ _ (pr1 p a))).
    + intro.
      exact (gtrunc _ _ _ _ _).
  - intros X.
    use funextsec.
    use gquot_ind_prop.
    + intros a.
      exact (pathscomp0rid _ @ ge _ _).
    + intro.
      exact (gtrunc _ _ _ _ _).
  - intros X Y Z f g.
    use funextsec.
    use gquot_ind_prop.
    + intros a.
      exact (pathscomp0rid _ @ ge _ _).
    + intro.
      exact (gtrunc _ _ _ _ _).
Qed.

Definition id_gquot
  : pstrans
      (ps_comp (⟦ I ⟧) gquot_psfunctor)
      (ps_comp gquot_psfunctor ⦃ I ⦄).
Proof.
  use make_pstrans.
  - exact id_gquot_data.
  - exact id_gquot_is_pstrans.
Defined.
