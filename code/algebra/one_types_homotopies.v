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
           (p : homot_endpoint l r al ar sl sr)
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
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - exact (idpath (sem_endpoint_one_types e X z)).
  - exact (!IHp).
  - exact (IHP₁ @ IHP₂).
  - apply idpath.
  - apply idpath.
  - apply idpath.
  - exact (maponpaths pr1 IHp).
  - exact (maponpaths dirprod_pr2 IHp).
  - exact (pathsdirprod IHp₁ IHp₂).
  - exact (maponpaths inl IHp).
  - exact (maponpaths inr IHp).
  - exact (pX j ((pr111 (sem_endpoint_one_types e)) X z)).
  - exact (maponpaths (pr2 X) IHp).
  - exact p_arg.
Defined.

(** Bicategory of prealgebras *)
Definition hit_prealgebra_one_types
           (Σ : hit_signature)
  : bicat
  := total_bicat (disp_alg_bicat (⟦ point_constr Σ ⟧)).

(** Projections and builders of prealgebras *)
Section HITPreAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_prealgebra_one_types Σ).

  Definition prealg_carrier
    : one_type
    := pr1 X.

  Definition prealg_constr
    : poly_act (point_constr Σ) prealg_carrier → prealg_carrier
    := pr2 X.
End HITPreAlgebraProjections.

Arguments prealg_constr {_ _} _.

Definition make_hit_prealgebra
           {Σ : hit_signature}
           (X : UU)
           (HX : isofhlevel 3 X)
           (f : poly_act (point_constr Σ) X → X)
  : hit_prealgebra_one_types Σ.
Proof.
  use tpair.
  - use make_one_type.
    + exact X.
    + exact HX.
  - exact f.
Defined.

Section HITPreAlgebraMorProjections.
  Context {Σ : hit_signature}
          {X Y : hit_prealgebra_one_types Σ}
          (f : X --> Y).

  Definition prealg_map_carrier
    : prealg_carrier X → prealg_carrier Y
    := pr1 f.

  Definition prealg_map_commute
    : ∏ (x : poly_act (point_constr Σ) (prealg_carrier X)),
      prealg_map_carrier (prealg_constr x)
      =
      prealg_constr (poly_map (point_constr Σ) prealg_map_carrier x)
    := pr12 f.
End HITPreAlgebraMorProjections.

Definition make_hit_prealgebra_mor
           {Σ : hit_signature}
           {X Y : hit_prealgebra_one_types Σ}
           (f : prealg_carrier X → prealg_carrier Y)
           (Hf : ∏ (x : poly_act (point_constr Σ) (prealg_carrier X)),
                 f (prealg_constr x)
                 =
                 prealg_constr (poly_map (point_constr Σ) f x))
  : X --> Y.
Proof.
  use tpair.
  - exact f.
  - use make_invertible_2cell.
    + exact Hf.
    + apply one_type_2cell_iso.
Defined.

(** Path Algebras for a HIT signature *)
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

(** Projections *)
Section HITPathAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_path_algebra_one_types Σ).

  Definition path_alg_carrier
    : one_type
    := prealg_carrier (pr1 X).

  Definition path_alg_constr
    : poly_act (point_constr Σ) path_alg_carrier → path_alg_carrier
    := @prealg_constr _ (pr1 X).

  Definition path_alg_path
             (j : path_label Σ)
             (x : poly_act (path_source Σ j) path_alg_carrier)
    : sem_endpoint_one_types (path_left Σ j) (pr1 X) x
      =
      sem_endpoint_one_types (path_right Σ j) (pr1 X) x
    := pr2 X j x.
End HITPathAlgebraProjections.

Arguments path_alg_constr {_ _} _.

Definition make_hit_path_algebra
           {Σ : hit_signature}
           (X : hit_prealgebra_one_types Σ)
           (pX : ∏ (j : path_label Σ)
                   (x : poly_act (path_source Σ j) (prealg_carrier X)),
                 sem_endpoint_one_types (path_left Σ j) _ x
                 =
                 sem_endpoint_one_types (path_right Σ j) _ x)
  : hit_path_algebra_one_types Σ.
Proof.
  use tpair.
  - exact X.
  - exact pX.
Defined.           

Section HITPathAlgebraMorProjections.
  Context {Σ : hit_signature}
          {X Y : hit_path_algebra_one_types Σ}
          (f : X --> Y).

  Definition path_alg_map_carrier
    : path_alg_carrier X → path_alg_carrier Y
    := prealg_map_carrier (pr1 f).

  Definition path_alg_map_commute
    : ∏ (x : poly_act (point_constr Σ) (path_alg_carrier X)),
      path_alg_map_carrier (path_alg_constr x)
      =
      path_alg_constr (poly_map (point_constr Σ) path_alg_map_carrier x)
    := prealg_map_commute (pr1 f).

  Definition path_alg_map_path
             (j : path_label Σ)
             (x : poly_act (path_source Σ j) (path_alg_carrier X))
    : maponpaths
        (pr11 f) (pr2 X j x) @
        pr1 (psnaturality_of (sem_endpoint_one_types (path_right Σ j)) (pr1 f)) x
      =
      pr1 (psnaturality_of (sem_endpoint_one_types (path_left Σ j)) (pr1 f)) x @
          pr2 Y j (poly_map (path_source Σ j) (pr11 f) x)
    := eqtohomot (pr2 f j) x.
End HITPathAlgebraMorProjections.

Definition make_hit_path_alg_map
           {Σ : hit_signature}
           {X Y : hit_path_algebra_one_types Σ}
           (f : pr1 X --> pr1 Y)
           (pf : ∏ (i : path_label Σ)
                   (j : poly_act (path_source Σ i) (path_alg_carrier X)),
                 (maponpaths (pr1 f) (pr2 X i j))
                   @ pr1 (psnaturality_of (sem_endpoint_one_types (path_right Σ i)) f) j
                 =
                 (pr1 (psnaturality_of (sem_endpoint_one_types (path_left Σ i)) f) j)
                   @ pr2 Y i (poly_map (path_source Σ i) (pr1 f) j))
  : X --> Y
  := f ,, λ i, funextsec _ _ _ (pf i).

(** HIT algebras *)
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

(** Projections *)
Section HITAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_algebra_one_types Σ).

  Definition alg_carrier
    : UU
    := path_alg_carrier (pr1 X).

  Definition alg_constr
    : poly_act (point_constr Σ) alg_carrier → alg_carrier
    := @path_alg_constr _ (pr1 X).

  Definition alg_path
             (j : path_label Σ)
             (x : poly_act (path_source Σ j) alg_carrier)
    : sem_endpoint_one_types (path_left Σ j) _ x
      =
      sem_endpoint_one_types (path_right Σ j) _ x
    := path_alg_path (pr1 X) j x.
  
  Definition alg_homot
    : is_hit_algebra_one_types Σ (pr1 X)
    := pr2 X.
End HITAlgebraProjections.

Definition make_algebra
           {Σ : hit_signature}
           (X : hit_path_algebra_one_types Σ)
           (hX : is_hit_algebra_one_types Σ X)
  : hit_algebra_one_types Σ
  := X ,, hX.

Definition make_algebra_map
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           (f : pr1 X --> pr1 Y)
  : X --> Y
  := f ,, tt.

(** Univalence of the bicategory of algebras *)
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
