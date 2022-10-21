(**
Here we define the bicategory of groupoids.
Note: this bicategory is not univalent since the groupoids are not univalent.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.

Local Open Scope cat.

Definition grpd_prebicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact groupoid.
  - exact (λ G₁ G₂, G₁ ⟶ G₂).
  - exact (λ _ _ F₁ F₂, pr1 F₁ ⟹ pr1 F₂).
  - exact (λ G, functor_identity _).
  - exact (λ _ _ _ F₁ F₂, F₁ ∙ F₂).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ α β, nat_trans_comp _ _ _ α β).
  - exact (λ _ _ _ F _ _ α, pre_whisker F α).
  - exact (λ _ _ _ _ _ H α, post_whisker α H).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
Defined.

Definition grpd_prebicat_laws
  : prebicat_laws grpd_prebicat_data.
Proof.
  repeat split; cbn.
  - intros C D F G η.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply id_left.
  - intros C D F G η.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply id_right.
  - intros C D F₁ F₂ F₃ F₄ α β γ.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply assoc.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq.
    { apply homset_property. }
    reflexivity.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply functor_id.
  - intros C₁ C₂ C₃ F G₁ G₂ G₃ α β.
    apply nat_trans_eq.
    { apply homset_property. }
    reflexivity.
  - intros C₁ C₂ C₃ F₁ F₂ F₃ G α β.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    exact (!(functor_comp G _ _)).
  - intros C D F G α.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C D F G α.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F G H₁ H₂ α.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ H α.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G H α.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ F₁ F₂ G₁ H₂ α β.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    exact ((nat_trans_ax β _ _ _)).
  - intros C D F.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    exact (id_left _ @ functor_id G _).
  - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄.
    apply nat_trans_eq.
    { apply homset_property. }
    intros ; cbn.
    rewrite !id_left.
    exact (functor_id F₄ _).
Qed.

Definition grpd_prebicat
  : prebicat.
Proof.
  use tpair.
  - exact grpd_prebicat_data.
  - exact grpd_prebicat_laws.
Defined.

Lemma isaset_cells_grpd_prebicat : isaset_cells grpd_prebicat.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition grpd_bicat
  : bicat.
Proof.
  use tpair.
  - exact grpd_prebicat.
  - exact isaset_cells_grpd_prebicat.
Defined.

Definition make_grpd_bicat
           (X : UU)
           (M : X → X → UU)
           (idX : ∏ (x : X), M x x)
           (invX : ∏ (x y : X), M x y → M y x)
           (cX : ∏ (x y z : X), M x y → M y z → M x z)
           (cidX : ∏ (x y : X) (f : M x y), cX _ _ _ f (idX y) = f)
           (idcX : ∏ (x y : X) (f : M x y), cX _ _ _ (idX x) f = f)
           (ccX : ∏ (w x y z : X)
                    (f : M w x) (g : M x y) (h : M y z),
                  cX _ _ _ f (cX _ _ _ g h)
                  =
                  cX _ _ _ (cX _ _ _ f g) h)
           (cinvX : ∏ (x y : X) (f : M x y), cX _ _ _ f (invX _ _ f) = idX _)
           (invcX : ∏ (x y : X) (f : M x y), cX _ _ _ (invX _ _ f) f = idX _)
           (isasetM : ∏ (x y : X), isaset (M x y))
  : grpd_bicat.
Proof.
  use make_groupoid.
  - use make_category.
    + use make_precategory.
      * use make_precategory_data.
        ** use make_precategory_ob_mor.
           *** exact X.
           *** exact M.
        ** exact idX.
        ** exact cX.
      * use make_is_precategory.
        ** exact idcX.
        ** exact cidX.
        ** exact ccX.
        ** intros w x y z f g h.
           exact (!(ccX w x y z f g h)).
    + exact isasetM.
  - intros x y f.
    use make_is_z_isomorphism.
    + exact (invX _ _ f).
    + split.
      * exact (cinvX _ _ f).
      * exact (invcX _ _ f).
Defined.

(** Every 2-cell is invertible. *)
Definition grpd_bicat_is_invertible_2cell
           {G₁ G₂ : grpd_bicat}
           {F₁ F₂ : G₁ --> G₂}
           (α : F₁ ==> F₂)
  : is_invertible_2cell α.
Proof.
  use make_is_invertible_2cell.
  - use make_nat_trans.
    + intros X.
      exact (inv_from_z_iso (_ ,, pr2 G₂ _ _ (pr1 α X))).
    + abstract
        (intros X Y f ; cbn ;
         refine (!_) ;
         apply z_iso_inv_on_right ;
         rewrite !assoc ;
         apply z_iso_inv_on_left ;
         simpl ;
         exact (!(pr2 α X Y f))).
  - abstract
      (apply nat_trans_eq ; try apply homset_property ;
       intro x ; cbn ;
       exact (z_iso_inv_after_z_iso (_ ,, _))).
  - abstract
      (apply nat_trans_eq ; try apply homset_property ;
       intro x ; cbn ;
       exact (z_iso_after_z_iso_inv (_ ,, _))).
Defined.

Definition groupoid_cancel
           {G : groupoid}
           {a b c : G}
           (f₁ f₂ : a --> b)
           (g : b --> c)
  : f₁ · g = f₂ · g → f₁ = f₂.
Proof.
  intro H.
  refine (!(id_right _) @ _).
  simple refine (maponpaths (λ x, _ · x) (!(z_iso_inv_after_z_iso (g ,, _))) @ _).
  { apply G. }
  simpl.
  refine (assoc _ _ _ @ _).
  refine (maponpaths (λ x, x · _) H @ _).
  refine (assoc' _ _ _ @ _).
  refine (maponpaths (λ x, _ · x) (z_iso_inv_after_z_iso (g ,, _)) @ _).
  apply id_right.
Qed.
