(** Interpretation of endpoints in 1-types *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
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
           (z : poly_act Q (pr11 X))
           (p_arg : pr1 (sem_endpoint_grpd al X) z
                    -->
                    pr1 (sem_endpoint_grpd ar X) z)
  : pr1 (sem_endpoint_grpd sl X) z --> pr1 (sem_endpoint_grpd sr X) z.
Proof.
  induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - (* identity *)
    apply poly_act_identity.
  - (* symmetry *)
    exact (poly_act_inverse IHp).
  - (* transitivity *)
    exact (poly_act_compose IHP₁ IHP₂).
  - (* associativity *)
    apply poly_act_identity.
  - (* left identity *)
    apply poly_act_identity.
  - (* right identity *)
    apply poly_act_identity.
  - (* first projection *)
    exact (pr1 IHp).
  - (* second projection *)
    exact (pr2 IHp).
  - (* pair of endpoints *)
    exact (IHp₁ ,, IHp₂).
  - (* left inclusion *)
    exact IHp.
  - (* right inclusion *)
    exact IHp.
  - (* path constructor *)
    exact (pX j _).
  - (* point constructor *)
    exact (#(pr2 X : _ ⟶ _) IHp).
  - (* path argument *)
    exact p_arg.
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
         · pr1 (pr2 G₂ j) (poly_map (path_source Σ j) (pr111 F) x).
  Proof.
    exact (nat_trans_eq_pointwise (pr2 F j) x).
  Qed.
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
       (z : poly_act (homot_point_arg Σ j) (pr111 X))
       (p : pr1 (sem_endpoint_grpd (homot_path_arg_left Σ j) (pr1 X)) z
            -->
            pr1 (sem_endpoint_grpd (homot_path_arg_right Σ j) (pr1 X)) z),
     sem_homot_endpoint_grpd
       (homot_left_path Σ j) (pr1 X) (pr2 X) z p
     =
     sem_homot_endpoint_grpd
       (homot_right_path Σ j) (pr1 X) (pr2 X) z p.

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

Definition hit_prealg_is_invertible_2cell
           (Σ : hit_signature)
           {X Y : hit_prealgebra_grpd Σ}
           {f g : X --> Y}
           (α : f ==> g)
  : is_invertible_2cell α.
Proof.
  use is_invertible_disp_to_total.
  use tpair.
  - apply grpd_bicat_is_invertible_2cell.
  - exact (disp_locally_groupoid_alg
             ⦃ point_constr Σ ⦄
             (pr1 X) (pr1 Y)
             (pr1 f) (pr1 g)
             (make_invertible_2cell
                (grpd_bicat_is_invertible_2cell (pr1 α)))
             (pr2 X) (pr2 Y)
             (pr2 f) (pr2 g)
             (pr2 α)).
Defined.

Definition hit_path_alg_is_invertible_2cell
           (Σ : hit_signature)
           {X Y : hit_path_algebra_grpd Σ}
           {f g : X --> Y}
           (α : f ==> g)
  : is_invertible_2cell α.
Proof.
  use is_invertible_disp_to_total.
  use tpair.
  - apply hit_prealg_is_invertible_2cell.
  - exact (disp_locally_groupoid_depprod
             (path_label Σ)
             (λ i, add_cell_disp_cat _ _ _ _ _)
             (λ i, disp_locally_groupoid_add_cell _ _ _ _ _)
             (pr1 X) (pr1 Y)
             (pr1 f) (pr1 g)
             (make_invertible_2cell
                (hit_prealg_is_invertible_2cell Σ (pr1 α)))
             (pr2 X) (pr2 Y)
             (pr2 f) (pr2 g)
             (pr2 α)).
Defined.

Definition hit_alg_is_invertible_2cell
           (Σ : hit_signature)
           {X Y : hit_algebra_grpd Σ}
           {f g : X --> Y}
           (α : f ==> g)
  : is_invertible_2cell α.
Proof.
  apply bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell.
  apply hit_path_alg_is_invertible_2cell.
Defined.
