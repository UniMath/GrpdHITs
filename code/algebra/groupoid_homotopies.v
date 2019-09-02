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
           (p : homot_endpoint l r al ar sl sr)
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
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - exact (nat_trans_id (pr1 ((sem_endpoint_grpd e) X))).
  - exact (@inv_cell grpd_bicat _ _ _ _ IHp (grpd_bicat_is_invertible_2cell _)).
  - exact (nat_trans_comp _ _ _ IHP₁ IHP₂).
  - apply nat_trans_functor_assoc.
  - apply nat_trans_functor_id_left.
  - apply nat_trans_functor_id_right.
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

(** Projections and builders of prealgebras *)
Section HITPreAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_prealgebra_grpd Σ).

  Definition prealg_carrier_grpd
    : groupoid
    := pr1 X.

  Definition prealg_constr_grpd
    : (⦃ point_constr Σ ⦄ prealg_carrier_grpd : groupoid) ⟶ prealg_carrier_grpd
    := pr2 X.
End HITPreAlgebraProjections.

Definition make_hit_prealgebra_grpd
           {Σ : hit_signature}
           (G : groupoid)
           (f : (⦃ point_constr Σ ⦄ G : groupoid) ⟶ G)
  : hit_prealgebra_grpd Σ
  := G ,, f.

Section HITPreAlgebraMorProjections.
  Context {Σ : hit_signature}
          {X Y : hit_prealgebra_grpd Σ}
          (f : X --> Y).

  Definition prealg_map_carrier_grpd
    : prealg_carrier_grpd X ⟶ prealg_carrier_grpd Y
    := pr1 f.

  Definition prealg_map_commute_grpd
    : prealg_constr_grpd X ∙ prealg_map_carrier_grpd
      ⟹
      # ⦃ point_constr Σ ⦄ prealg_map_carrier_grpd ∙ prealg_constr_grpd Y
    := pr12 f.
End HITPreAlgebraMorProjections.

Definition make_hit_prealgebra_mor
           {Σ : hit_signature}
           {G₁ G₂ : hit_prealgebra_grpd Σ}
           (f : prealg_carrier_grpd G₁ ⟶ prealg_carrier_grpd G₂)
           (Hf : prealg_constr_grpd G₁ ∙ f
                 ⟹
                 # ⦃ point_constr Σ ⦄ f ∙ prealg_constr_grpd G₂)
  : G₁ --> G₂.
Proof.
  use tpair.
  - exact f.
  - use make_invertible_2cell.
    + exact Hf.
    + apply grpd_bicat_is_invertible_2cell.
Defined.

(** Bicategory of path algebras *)
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

(** Projections *)
Section HITPathAlgebraProjections.
  Context {Σ : hit_signature}
          (G : hit_path_algebra_grpd Σ).

  Definition path_alg_carrier_grpd
    : groupoid
    := prealg_carrier_grpd (pr1 G).

  Definition path_alg_constr_grpd
    : (⦃ point_constr Σ ⦄ path_alg_carrier_grpd : groupoid) ⟶ path_alg_carrier_grpd
    := prealg_constr_grpd (pr1 G).

  Definition path_alg_path_grpd
             (j : path_label Σ)
    : pr1 (sem_endpoint_grpd (path_left Σ j) (pr1 G))
      ⟹
      pr1 (sem_endpoint_grpd (path_right Σ j) (pr1 G))
    := pr2 G j.
End HITPathAlgebraProjections.

Definition make_hit_path_algebra_grpd
           {Σ : hit_signature}
           (G : hit_prealgebra_grpd Σ)
           (pG : ∏ (j : path_label Σ),
                 pr1 (sem_endpoint_grpd (path_left Σ j) G)
                 ⟹
                 pr1 (sem_endpoint_grpd (path_right Σ j) G))
  : hit_path_algebra_grpd Σ
  := G ,, pG.

Section HITPathAlgebraMorProjections.
  Context {Σ : hit_signature}
          {G₁ G₂ : hit_path_algebra_grpd Σ}
          (F : G₁ --> G₂).

  Definition path_alg_map_carrier_grpd
    : path_alg_carrier_grpd G₁ ⟶ path_alg_carrier_grpd G₂
    := prealg_map_carrier_grpd (pr1 F).

  Definition path_alg_map_commute_grpd
    : prealg_constr_grpd (pr1 G₁) ∙ path_alg_map_carrier_grpd
      ⟹
      # ⦃ point_constr Σ ⦄ path_alg_map_carrier_grpd ∙ prealg_constr_grpd (pr1 G₂)
    := prealg_map_commute_grpd (pr1 F).

  Definition path_alg_map_path_grpd
             (j : path_label Σ)
             (x : poly_act (path_source Σ j) (pr111 G₁))
    : # (pr111 F) (pr1 (pr2 G₁ j) x)
    · pr11 (psnaturality_of (sem_endpoint_grpd (path_right Σ j)) (pr1 F)) x
    =
    pr11 (psnaturality_of (sem_endpoint_grpd (path_left Σ j)) (pr1 F)) x
         · pr1 (pr2 G₂ j) (poly_map (path_source Σ j) (pr111 F) x)
    := nat_trans_eq_pointwise (pr2 F j) x.
End HITPathAlgebraMorProjections.

Definition make_hit_path_alg_map_grpd
           {Σ : hit_signature}
           {G₁ G₂ : hit_path_algebra_grpd Σ}
           (F : pr1 G₁ --> pr1 G₂)
           (pf : ∏ (j : path_label Σ)
                   (x : poly_act (path_source Σ j) (pr111 G₁)),
                 # (pr11 F) (pr1 (pr2 G₁ j) x)
                 · pr11 (psnaturality_of (sem_endpoint_grpd (path_right Σ j)) F) x
                 =
                 pr11 (psnaturality_of (sem_endpoint_grpd (path_left Σ j)) F) x
                 · pr1 (pr2 G₂ j) (poly_map (path_source Σ j) (pr111 F) x))
  : G₁ --> G₂.
Proof.
  use tpair.
  - exact F.
  - intro j.
    use nat_trans_eq.
    { apply homset_property. }
    exact (pf j).
Defined.

(** Bicategory of algebras *)
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

(** Projections *)
Section HITAlgebraProjections.
  Context {Σ : hit_signature}
          (G : hit_algebra_grpd Σ).

  Definition alg_carrier_grpd
    : groupoid
    := path_alg_carrier_grpd (pr1 G).

  Definition alg_constr_grpd
    : (⦃ point_constr Σ ⦄ (path_alg_carrier_grpd (pr1 G)) : groupoid)
      ⟶
      path_alg_carrier_grpd (pr1 G)
    := path_alg_constr_grpd (pr1 G).

  Definition alg_path_grpd
             (j : path_label Σ)
    : pr1 (sem_endpoint_grpd (path_left Σ j) (pr11 G))
      ⟹
      pr1 (sem_endpoint_grpd (path_right Σ j) (pr11 G))
    := path_alg_path_grpd (pr1 G) j.
  
  Definition alg_homot_grpd
    : is_hit_algebra_grpd Σ (pr1 G)
    := pr2 G.
End HITAlgebraProjections.

Definition make_algebra_grpd
           {Σ : hit_signature}
           (X : hit_path_algebra_grpd Σ)
           (hX : is_hit_algebra_grpd Σ X)
  : hit_algebra_grpd Σ
  := X ,, hX.

Definition make_algebra_map_grpd
           {Σ : hit_signature}
           {X Y : hit_algebra_grpd Σ}
           (f : pr1 X --> pr1 Y)
  : X --> Y
  := f ,, tt.
