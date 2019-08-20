(** Interpretation of endpoints in 1-types *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
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
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.

Local Open Scope cat.

(** Needed natural transformations *)
Definition pr1_pair_functor_comp
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : pair_functor_data F₁ F₂
                ⟹
                pair_functor_data G₁ G₂)
  : nat_trans_data F₁ G₁
  := λ x, pr1 (α x).

Definition pr1_pair_functor_is_nat_trans
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : pair_functor_data F₁ F₂
                ⟹
                pair_functor_data G₁ G₂)
  : is_nat_trans _ _ (pr1_pair_functor_comp α).
Proof.
  exact (λ x y f, maponpaths pr1 (pr2 α x y f)).
Qed.

Definition pr1_pair_functor
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : pair_functor_data F₁ F₂
                ⟹
                pair_functor_data G₁ G₂)
  : F₁ ⟹ G₁.
Proof.
  use make_nat_trans.
  - exact (pr1_pair_functor_comp α).
  - exact (pr1_pair_functor_is_nat_trans α).
Defined.

Definition pr2_pair_functor_comp
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : pair_functor_data F₁ F₂
                ⟹
                pair_functor_data G₁ G₂)
  : nat_trans_data F₂ G₂
  := λ x, pr2 (α x).

Definition pr2_pair_functor_is_nat_trans
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : pair_functor_data F₁ F₂
                ⟹
                pair_functor_data G₁ G₂)
  : is_nat_trans _ _ (pr2_pair_functor_comp α).
Proof.
  exact (λ x y f, maponpaths dirprod_pr2 (pr2 α x y f)).
Qed.

Definition pr2_pair_functor
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : pair_functor_data F₁ F₂
                ⟹
                pair_functor_data G₁ G₂)
  : F₂ ⟹ G₂.
Proof.
  use make_nat_trans.
  - exact (pr2_pair_functor_comp α).
  - exact (pr2_pair_functor_is_nat_trans α).
Defined.

Definition pair_nat_trans_data
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : F₁ ⟹ G₁)
           (β : F₂ ⟹ G₂)
  : nat_trans_data (pair_functor F₁ F₂) (pair_functor G₁ G₂)
  := λ x, α x ,, β x.

Definition pair_nat_trans_is_nat_trans
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : F₁ ⟹ G₁)
           (β : F₂ ⟹ G₂)
  : is_nat_trans _ _ (pair_nat_trans_data α β).
Proof.
  intros x y f.
  exact (pathsdirprod (pr2 α x y f) (pr2 β x y f)).
Qed.  

Definition pair_nat_trans
           {C D₁ D₂ : category}
           {F₁ G₁ : C ⟶ D₁}
           {F₂ G₂ : C ⟶ D₂}
           (α : F₁ ⟹ G₁)
           (β : F₂ ⟹ G₂)
  : pair_functor F₁ F₂ ⟹ pair_functor G₁ G₂.
Proof.
  use make_nat_trans.
  - exact (pair_nat_trans_data α β).
  - exact (pair_nat_trans_is_nat_trans α β).
Defined.

(** Now we combine it *)
Definition sem_homot_endpoint_grpd
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
           (X : total_bicat (disp_alg_bicat (⦃ A ⦄)))
           (pX : ∏ (j : J),
                 pr1 (pr111 (sem_endpoint_grpd (l j)) X)
                 ⟹
                 pr1 (pr111 (sem_endpoint_grpd (r j)) X))
           (p_arg : pr1 (sem_endpoint_grpd al X)
                    ⟹
                    pr1 (sem_endpoint_grpd ar X))
  : pr1 (sem_endpoint_grpd sl X) ⟹ pr1 (sem_endpoint_grpd sr X).
Proof.
  induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - exact (nat_trans_id (pr1 ((sem_endpoint_grpd e) X))).
  - exact (@inv_cell grpd_bicat _ _ _ _ IHp (grpd_bicat_is_invertible_2cell _)).
  - exact (nat_trans_comp _ _ _ IHP₁ IHP₂).
  - exact (pr1_pair_functor IHp).
  - exact (pr2_pair_functor IHp).
  - exact (pair_nat_trans IHp₁ IHp₂).
  - exact (post_whisker IHp (inl_grpd_transformation T₁ T₂ (pr1 X))).
  - exact (post_whisker IHp (inr_grpd_transformation T₁ T₂ (pr1 X))).
  - exact (pre_whisker (pr1 (pr111 (sem_endpoint_grpd e) X)) (pX j)).
  - exact (post_whisker IHp (pr2 X)).
  - exact p_arg.
Defined.

(** Bicategory of algebras *)
Definition hit_prealgebra_grpd
           (Σ : hit_signature)
  : bicat
  := total_bicat (disp_alg_bicat (⦃ point_constr Σ ⦄)).

Definition hit_path_algebra_disp_grpd
           (Σ : hit_signature)
  : disp_bicat (hit_prealgebra_grpd Σ)
  := disp_depprod_bicat
       (path_label Σ)
       (λ j, add_cell_disp_cat
               _ _ _
               (sem_endpoint_grpd (path_left Σ j))
               (sem_endpoint_grpd (path_right Σ j))).

Definition hit_path_algebra_grpd
           (Σ : hit_signature)
  : bicat
  := total_bicat (hit_path_algebra_disp_grpd Σ).

Definition is_hit_algebra_grpd
           (Σ : hit_signature)
           (X : hit_path_algebra_grpd Σ)
  : UU
  := ∏ (j : homot_label Σ)
       (p : pr1 (sem_endpoint_grpd (homot_path_arg_left Σ j) (pr1 X))
                ⟹
                pr1 (sem_endpoint_grpd (homot_path_arg_right Σ j) (pr1 X)))
       (z : poly_act (homot_point_arg Σ j) (pr111 X)),
     sem_homot_endpoint_grpd
       (homot_left_path Σ j) (pr1 X) (pr2 X) p z
     =
     sem_homot_endpoint_grpd
       (homot_right_path Σ j) (pr1 X) (pr2 X) p z.

Definition hit_algebra_grpd
           (Σ : hit_signature)
  : bicat
  := fullsubbicat (hit_path_algebra_grpd Σ) (is_hit_algebra_grpd Σ).
