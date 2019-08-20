(** Interpretation of endpoints in 1-types *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.

Local Open Scope cat.

Definition sem_homot_endpoint_one_types
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l : ∏ (j : J), endpoint A (S j) I}
           {r : ∏ (j : J), endpoint A (S j) I}
           {Q : poly_code}
           {TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : poly_code}
           {sl sr : endpoint A Q T}
           (p : homot_endpoint A J S l r Q TR al ar T sl sr)
           (X : total_bicat (disp_alg_bicat (⟦ A ⟧)))
           (pX : ∏ (i : J),
                 sem_endpoint_one_types (l i) X
                 ~
                 sem_endpoint_one_types (r i) X)
           (z : poly_act Q (pr1 X : one_type))
           (p_arg : sem_endpoint_one_types al X z = sem_endpoint_one_types ar X z)
  : sem_endpoint_one_types sl X z = sem_endpoint_one_types sr X z.
Proof.
  induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - exact (idpath (sem_endpoint_one_types e X z)).
  - exact (!IHp).
  - exact (IHP₁ @ IHP₂).
  - exact (maponpaths pr1 IHp).
  - exact (maponpaths dirprod_pr2 IHp).
  - exact (pathsdirprod IHp₁ IHp₂).
  - exact (maponpaths inl IHp).
  - exact (maponpaths inr IHp).
  - exact (pX j ((pr111 (sem_endpoint_one_types e)) X z)).
  - exact (maponpaths (pr2 X) IHp).
  - exact p_arg.
Defined.

Definition hit_prealgebra_one_types
           (Σ : hit_signature)
  : bicat
  := total_bicat (disp_alg_bicat (⟦ point_constr Σ ⟧)).

Definition hit_path_algebra_disp_one_types
           (Σ : hit_signature)
  : disp_bicat (hit_prealgebra_one_types Σ)
  := disp_depprod_bicat
       (path_label Σ)
       (λ j, add_cell_disp_cat
               _ _ _
               (sem_endpoint_one_types (path_left Σ j))
               (sem_endpoint_one_types (path_right Σ j))).

Definition hit_path_algebra_one_types
           (Σ : hit_signature)
  : bicat
  := total_bicat (hit_path_algebra_disp_one_types Σ).

Definition is_hit_algebra_one_types
           (Σ : hit_signature)
           (X : hit_path_algebra_one_types Σ)
  : UU
  := ∏ (j : homot_label Σ)
       (x : ⟦ homot_point_arg Σ j ⟧ (pr11 X) : one_type)
       (p : sem_endpoint_one_types (homot_path_arg_left Σ j) (pr1 X) x
            =
            sem_endpoint_one_types (homot_path_arg_right Σ j) (pr1 X) x),
     sem_homot_endpoint_one_types
       (homot_left_path Σ j) (pr1 X) (pr2 X) x p
     =
     sem_homot_endpoint_one_types
       (homot_right_path Σ j) (pr1 X) (pr2 X) x p.

Definition isaprop_is_hit_algebra_one_types
           (Σ : hit_signature)
           (X : hit_path_algebra_one_types Σ)
  : isaprop (is_hit_algebra_one_types Σ X).
Proof.
  do 3 (use impred ; intro).
  exact (one_type_isofhlevel (pr11 X) _ _ _ _).
Defined.

Definition hit_algebra_one_types
           (Σ : hit_signature)
  : bicat
  := fullsubbicat (hit_path_algebra_one_types Σ) (is_hit_algebra_one_types Σ).

Definition is_univalent_2_hit_algebra_one_types
           (Σ : hit_signature)
  : is_univalent_2 (hit_algebra_one_types Σ).
Proof.
  use is_univalent_2_fullsubbicat.
  - use total_is_univalent_2.
    + split.
      * use disp_depprod_univalent_2_0.
        ** use total_is_univalent_2_1.
           *** apply one_types_is_univalent_2_1.
           *** apply disp_alg_bicat_univalent_2_1.
        ** intro i.
           apply add_cell_disp_cat_univalent_2_1.
        ** intro i.
           use add_cell_disp_cat_univalent_2_0.
           *** apply one_types_is_univalent_2_1.
           *** apply disp_alg_bicat_univalent_2_1.
      * use disp_depprod_univalent_2_1.
        intro i.
        apply add_cell_disp_cat_univalent_2_1.
    + split.
      * use total_is_univalent_2_0.
        ** apply one_types_is_univalent_2_0.
        ** apply disp_alg_bicat_univalent_2_0.
           apply one_types_is_univalent_2_1.
      * use total_is_univalent_2_1.
        ** apply one_types_is_univalent_2_1.
        ** apply disp_alg_bicat_univalent_2_1.
  - exact (isaprop_is_hit_algebra_one_types Σ).
Defined.
