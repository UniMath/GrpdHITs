(** Interpretation of endpoints in 1-types *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
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
  : sem_endpoint_one_types sl X z = sem_endpoint_one_types sr X z
  := sem_homot_endpoint_UU p (pr1 X : one_type) (pr2 X) pX z p_arg.

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

Definition preserves_point
           {Σ : hit_signature}
           {X Y : hit_prealgebra_one_types Σ}
           (f : prealg_carrier X → prealg_carrier Y)
  : UU
  := ∏ (x : poly_act (point_constr Σ) (prealg_carrier X)),
     f (prealg_constr x)
     =
     prealg_constr (poly_map (point_constr Σ) f x).

Section HITPreAlgebraMorProjections.
  Context {Σ : hit_signature}
          {X Y : hit_prealgebra_one_types Σ}
          (f : X --> Y).

  Definition prealg_map_carrier
    : prealg_carrier X → prealg_carrier Y
    := pr1 f.

  Definition prealg_map_commute
    : preserves_point prealg_map_carrier
    := pr12 f.
End HITPreAlgebraMorProjections.

Definition make_hit_prealgebra_mor
           {Σ : hit_signature}
           {X Y : hit_prealgebra_one_types Σ}
           (f : prealg_carrier X → prealg_carrier Y)
           (Hf : preserves_point f)
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

Definition preserves_path
           {Σ : hit_signature}
           {X Y : hit_path_algebra_one_types Σ}
           (f : pr1 X --> pr1 Y)
           (Hf : preserves_point (pr1 f))
  : UU
  := ∏ (j : path_label Σ)
       (x : poly_act (path_source Σ j) (path_alg_carrier X)),
     maponpaths (prealg_map_carrier f) (path_alg_path X j x)
     @ sem_endpoint_UU_natural (path_right Σ j) Hf x
     =
     sem_endpoint_UU_natural (path_left Σ j) Hf x
     @ path_alg_path Y j (poly_map (path_source Σ j) _ x).
  
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
    : preserves_path (pr1 f) path_alg_map_commute
    := λ j x, eqtohomot (pr2 f j) x.
End HITPathAlgebraMorProjections.

Definition make_hit_path_alg_map
           {Σ : hit_signature}
           {X Y : hit_path_algebra_one_types Σ}
           (f : pr1 X --> pr1 Y)
           (pf : preserves_path _ (prealg_map_commute f))
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

(** Projections of algebra maps *)
Section HITAlgebraMapProjections.
  Context {Σ : hit_signature}
          {X Y : hit_algebra_one_types Σ}
          (f : X --> Y).

  Definition alg_map_carrier
    : alg_carrier X → alg_carrier Y
    := path_alg_map_carrier (pr1 f).

  Definition alg_map_commute
    : preserves_point alg_map_carrier
    := path_alg_map_commute (pr1 f).

  Definition alg_map_path
    : preserves_path _ alg_map_commute
    := path_alg_map_path (pr1 f).
End HITAlgebraMapProjections.

Definition make_algebra_map
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           (f : pr1 X --> pr1 Y)
  : X --> Y
  := f ,, tt.

Definition is_algebra_2cell
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           {f g : X --> Y}
           (α : alg_map_carrier f ~ alg_map_carrier g)
  : UU
  := ∏ (z : poly_act (point_constr Σ) (alg_carrier X)),
     α (alg_constr X z)
     @ alg_map_commute g z
     =
     alg_map_commute f z
     @ maponpaths (alg_constr Y) (poly_homot (point_constr Σ) α z).

(** Projections of algebra 2-cells *)
Section HITAlgebraCellProjections.
  Context {Σ : hit_signature}
          {X Y : hit_algebra_one_types Σ}
          {f g : X --> Y}
          (α : f ==> g).

  Definition alg_2cell_carrier
    : alg_map_carrier f ~ alg_map_carrier g
    := pr111 α.

  Definition alg_2cell_commute
    : is_algebra_2cell alg_2cell_carrier
    := eqtohomot (pr211 α).
End HITAlgebraCellProjections.

(** Equality of algebra 2-cells *)
Definition algebra_2cell_eq
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           {f g : X --> Y}
           {α β : f ==> g}
           (p : alg_2cell_carrier α ~ alg_2cell_carrier β)
  : α = β.
Proof.
  use subtypePath.
  { intro ; apply isapropunit. }
  use subtypePath.
  { intro ; use impred ; intro ; apply isapropunit. }
  use subtypePath.
  { intro ; apply one_types. }
  use funextsec.
  exact p.
Qed.

Definition alg_2cell_eq_component
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           {f g : X --> Y}
           {α β : f ==> g}
           (p : α = β)
  : alg_2cell_carrier α ~ alg_2cell_carrier β.
Proof.
  exact (eqtohomot (maponpaths (λ z, pr111 z) p)).
Qed.

(** Builder of 2-cells of algebras *)
Definition make_algebra_2cell
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           {f g : X --> Y}
           (α : alg_map_carrier f ~ alg_map_carrier g)
           (Hα : is_algebra_2cell α)
  : f ==> g.
Proof.
  simple refine (((α ,, _) ,, λ _, tt) ,, tt).
  abstract (use funextsec ; exact Hα).
Defined.

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

Definition hit_prealg_is_invertible_2cell_one_type
           (Σ : hit_signature)
           {X Y : hit_prealgebra_one_types Σ}
           {f g : X --> Y}
           (α : f ==> g)
  : is_invertible_2cell α.
Proof.
  use is_invertible_disp_to_total.
  use tpair.
  - apply one_type_2cell_iso.
  - exact (disp_locally_groupoid_alg
             (⟦ point_constr Σ ⟧)
             (pr1 X) (pr1 Y)
             (pr1 f) (pr1 g)
             (make_invertible_2cell
                (one_type_2cell_iso _ _ _ _ (pr1 α)))
             (pr2 X) (pr2 Y)
             (pr2 f) (pr2 g)
             (pr2 α)).
Defined.

Definition hit_path_alg_is_invertible_2cell_one_type
           (Σ : hit_signature)
           {X Y : hit_path_algebra_one_types Σ}
           {f g : X --> Y}
           (α : f ==> g)
  : is_invertible_2cell α.
Proof.
  use is_invertible_disp_to_total.
  use tpair.
  - apply hit_prealg_is_invertible_2cell_one_type.
  - exact (disp_locally_groupoid_depprod
             (path_label Σ)
             (λ i, add_cell_disp_cat _ _ _ _ _)
             (λ i, disp_locally_groupoid_add_cell _ _ _ _ _)
             (pr1 X) (pr1 Y)
             (pr1 f) (pr1 g)
             (make_invertible_2cell
                (hit_prealg_is_invertible_2cell_one_type Σ (pr1 α)))
             (pr2 X) (pr2 Y)
             (pr2 f) (pr2 g)
             (pr2 α)).
Defined.

Definition hit_alg_is_invertible_2cell_one_type
           (Σ : hit_signature)
           {X Y : hit_algebra_one_types Σ}
           {f g : X --> Y}
           (α : f ==> g)
  : is_invertible_2cell α.
Proof.
  apply bicat_is_invertible_2cell_to_fullsub_is_invertible_2cell.
  apply hit_path_alg_is_invertible_2cell_one_type.
Defined.
