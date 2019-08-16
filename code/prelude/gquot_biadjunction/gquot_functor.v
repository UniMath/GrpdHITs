Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.

Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.

Require Import prelude.cubical_methods.
Require Import prelude.grpd_bicat.
Require Import groupoid_quotient.gquot.
Require Import groupoid_quotient.gquot_principles.

Local Open Scope cat.

Section GQuotFunctor.
  Definition gquot_functor_obj (G : groupoid)
    : one_type.
  Proof.
    use make_one_type.
    - exact (gquot G).
    - exact (gtrunc G).
  Defined.

  Definition gquot_functor_map
             {G₁ G₂ : groupoid}
             (F : G₁ ⟶ G₂)
    : gquot_functor_obj G₁ → gquot_functor_obj G₂.
  Proof.
    use gquot_rec.
    - exact (λ x, gcl G₂ (F x)).
    - exact (λ _ _ f, gcleq G₂ (#F f)).
    - exact (λ x, maponpaths (gcleq G₂) (functor_id F x) @ ge G₂ (F x)).
    - exact (λ _ _ _ f g,
             (maponpaths (gcleq G₂) (functor_comp F f g))
               @ gconcat G₂ (#F f) (#F g)).
    - exact (gtrunc G₂).
  Defined.

  Definition gquot_functor_cell_po
             {G₁ G₂ : groupoid}
             {F₁ F₂ : G₁ ⟶ G₂}
             (α : F₁ ⟹ F₂)
             (x₁ x₂ : G₁)
             (f : x₁ --> x₂)
    : @PathOver
        (gquot G₁)
        (gcl G₁ x₁) (gcl G₁ x₂)
        (λ z : gquot G₁, gquot_functor_map F₁ z = gquot_functor_map F₂ z) 
        (gcleq G₂ (α x₁))
        (gcleq G₂ (α x₂))
        (gcleq G₁ f).
  Proof.
    apply map_PathOver.
    refine (whisker_square (idpath _)
                           (!_)
                           (!_)
                           (idpath _)
                           _).
    - exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    - exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    - refine (!(gconcat _ _ _) @ maponpaths (gcleq G₂) _ @ gconcat _ _ _).
      exact (pr2 α _ _ f).
  Qed.

  Definition gquot_functor_cell
             {G₁ G₂ : groupoid}
             {F₁ F₂ : G₁ ⟶ G₂}
             (α : F₁ ⟹ F₂)
    : ∏ (x : gquot G₁), gquot_functor_map F₁ x = gquot_functor_map F₂ x.
  Proof.
    use gquot_ind_set ; cbn.
    - exact (λ x, gcleq G₂ (α x)).
    - exact (gquot_functor_cell_po α).
    - intros x.
      exact (gtrunc G₂ _ _).
  Defined.

  Definition gquot_functor_identity_po
             {G : groupoid}
             (x₁ x₂ : G)
             (f : x₁ --> x₂)
    : @PathOver
        _
        (gcl G x₁) (gcl G x₂)
        (λ z, z = gquot_functor_map (functor_identity G) z) 
        (idpath (gcl G x₁))
        (idpath (gcl G x₂))
        (gcleq G f).
  Proof.
    apply map_PathOver.
    refine (whisker_square (idpath _)
                           (!(maponpathsidfun _))
                           (!_)
                           (idpath _)
                           (vrefl _)).
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  Qed.

  Definition gquot_functor_identity
             (G : groupoid)
    : ∏ (x : gquot G), x = gquot_functor_map (functor_identity G) x.
  Proof.
    use gquot_ind_set ; cbn.
    - exact (λ _, idpath _).
    - exact gquot_functor_identity_po.
    - intros x.
      exact (gtrunc G _ _).
  Defined.

  Definition gquot_functor_composition_po
             {G₁ G₂ G₃ : groupoid}
             (F₁ : G₁ ⟶ G₂)
             (F₂ : G₂ ⟶ G₃)
             (x₁ x₂ : G₁)
             (f : x₁ --> x₂)
    : @PathOver
        _
        (gcl G₁ x₁) (gcl G₁ x₂)
        (λ z,
         gquot_functor_map F₂ (gquot_functor_map F₁ z)
         =
         gquot_functor_map (F₁ ∙ F₂) z)
        (idpath (gcl G₃ (F₂ (F₁ x₁))))
        (idpath (gcl G₃ (F₂ (F₁ x₂))))
        (gcleq G₁ f).
  Proof.
    apply map_PathOver.
    refine (whisker_square (idpath _)
                           _
                           (!_)
                           (idpath _)
                           (vrefl _)).
    - unfold gquot_functor_map.
      refine (_ @ (maponpathscomp _ _ _)).
      refine (_ @ maponpaths (maponpaths _) (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))).
      exact (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)).
    - unfold gquot_functor_map.
      cbn.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  Qed.

  Definition gquot_functor_composition
             {G₁ G₂ G₃ : groupoid}
             (F₁ : G₁ ⟶ G₂)
             (F₂ : G₂ ⟶ G₃)
    : ∏ (x : gquot G₁),
      gquot_functor_map F₂ (gquot_functor_map F₁ x)
      =
      gquot_functor_map (F₁ ∙ F₂) x.
  Proof.
    use gquot_ind_set ; cbn.
    - exact (λ _, idpath _).
    - exact (gquot_functor_composition_po F₁ F₂).
    - intros x.
      exact (gtrunc G₃ _ _).
  Defined.

  Definition gquot_psfunctor_data
    : psfunctor_data grpd_bicat one_types.
  Proof.
    use make_psfunctor_data.
    - exact gquot_functor_obj.
    - exact @gquot_functor_map.
    - exact @gquot_functor_cell.
    - exact gquot_functor_identity.
    - exact @gquot_functor_composition.
  Defined.

  Definition gquot_psfunctor_is_psfunctor
    : psfunctor_laws gquot_psfunctor_data.
  Proof.
    repeat split.
    - intros G₁ G₂ F ; cbn.
      use funextsec.
      use gquot_ind_prop ; simpl.
      + exact (λ _, ge _ _).
      + intro x.
        exact (gtrunc G₂ _ _ _ _).
    - intros G₁ G₂ F₁ F₂ F₃ α₁ α₂ ; cbn.
      use funextsec.
      use gquot_ind_prop ; simpl.
      + exact (λ _, gconcat _ _ _).
      + intro x.
        exact (gtrunc G₂ _ _ _ _).
    - intros G₁ G₂ F ; cbn.
      use funextsec.
      use gquot_ind_prop ; simpl.
      + exact (λ _, !(ge _ _)).
      + intro x.
        exact (gtrunc G₂ _ _ _ _).
    - intros G₁ G₂ F ; cbn.
      use funextsec.
      use gquot_ind_prop ; simpl.
      + exact (λ _, !(ge _ _)).
      + intro x.
        exact (gtrunc G₂ _ _ _ _).
    - intros G₁ G₂ G₃ G₄ F₁ F₂ F₃ ; cbn.
      use funextsec.
      use gquot_ind_prop ; simpl.
      + exact (λ _, ge _ _).
      + intro x.
        exact (gtrunc G₄ _ _ _ _).
    - intros G₁ G₂ G₃ F E₁ E₂ α ; cbn.
      use funextsec.
      use gquot_ind_prop ; simpl.
      + exact (λ _, !(pathscomp0rid _)).
      + intro x.
        exact (gtrunc G₃ _ _ _ _).
    - intros G₁ G₂ G₃ F₁ F₂ E α ; cbn.
      use funextsec.
      use gquot_ind_prop ; simpl.
      + intros a ; cbn.
        unfold homotcomp, homotfun ; cbn.
        refine (!_ @ !(pathscomp0rid _)).
        unfold gquot_functor_map.
        rewrite gquot_rec_beta_gcleq.
        apply idpath.
      + intro x.
        exact (gtrunc G₃ _ _ _ _).
  Qed.
    
  Definition gquot_psfunctor
    : psfunctor grpd_bicat one_types.
  Proof.
    use make_psfunctor.
    - exact gquot_psfunctor_data.
    - exact gquot_psfunctor_is_psfunctor.
    - split ; cbn ; intros ; apply one_type_2cell_iso.
  Defined.
End GQuotFunctor.
