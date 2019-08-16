(** Interpretation of endpoints in groupoid *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Constant.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

(** Left inclusion *)
Definition inl_grpd_transformation_data_comp_data
           (P Q : poly_code)
           (G : groupoid)
  : functor_data (pr1 (⦃ P ⦄ G)) (pr1 (⦃ P + Q ⦄ G)).
Proof.
  use make_functor_data.
  - exact inl.
  - exact (λ _ _ f, f).
Defined.

Definition inl_grpd_transformation_data_comp_is_functor
           (P Q : poly_code)
           (G : groupoid)
  : is_functor (inl_grpd_transformation_data_comp_data P Q G).
Proof.
  split.
  - intros x.
    apply idpath.
  - intros x y z f g.
    apply idpath.
Qed.

Definition inl_grpd_transformation_data_comp
           (P Q : poly_code)
           (G : groupoid)
  : pr1 (⦃ P ⦄ G) ⟶ pr1 (⦃ P + Q ⦄ G).
Proof.
  use make_functor.
  - exact (inl_grpd_transformation_data_comp_data P Q G).
  - exact (inl_grpd_transformation_data_comp_is_functor P Q G).
Defined.

Definition inl_grpd_transformation_data_natural_data
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : nat_trans_data
      ((inl_grpd_transformation_data_comp P Q G₁)
         ∙ poly_act_functor (P + Q) _ _ F)
      ((poly_act_functor P _ _ F)
         ∙ inl_grpd_transformation_data_comp P Q G₂)
  := λ x, poly_act_identity P G₂ (poly_map P F x).

Definition inl_grpd_transformation_data_natural_is_nat_trans
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : is_nat_trans _ _ (inl_grpd_transformation_data_natural_data P Q G₁ G₂ F).
Proof.
  intros x y f.
  exact (poly_act_id_right _ _ _ _ _ @ !(poly_act_id_left _ _ _ _ _)).
Qed.

Definition inl_grpd_transformation_data_natural
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : inl_grpd_transformation_data_comp P Q G₁ ∙ poly_act_functor (P + Q) _ _ F
      ⟹
      poly_act_functor P _ _ F ∙ inl_grpd_transformation_data_comp P Q G₂.
Proof.
  use make_nat_trans.
  - exact (inl_grpd_transformation_data_natural_data P Q G₁ G₂ F).
  - exact (inl_grpd_transformation_data_natural_is_nat_trans P Q G₁ G₂ F).
Defined.
 
Definition inl_grpd_transformation_data
           (P Q : poly_code)
  : pstrans_data (⦃ P ⦄) (⦃ P + Q ⦄).
Proof.
  use make_pstrans_data.
  - exact (inl_grpd_transformation_data_comp P Q).
  - intros G₁ G₂ F.
    use make_invertible_2cell.
    + exact (inl_grpd_transformation_data_natural P Q G₁ G₂ F).
    + apply grpd_bicat_is_invertible_2cell.
Defined.

Definition inl_grpd_transformation_is_pstrans
           (P Q : poly_code)
  : is_pstrans (inl_grpd_transformation_data P Q).
Proof.
  repeat split.
  - intros X Y f g p.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (poly_act_id_right _ _ _ _ _ @ !(poly_act_id_left _ _ _ _ _)).
  - intros X.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact ((poly_act_id_right _ _ _ _ _)
             @ !(poly_act_id_left _ _ _ _ _)
             @ !(poly_act_id_left _ _ _ _ _)
             @ poly_act_assoc _ _ _ _ _ _ _ _ _).
  - intros X Y Z f g.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    simpl.
    refine ((poly_act_id_right _ _ _ _ _)
              @ !_).
    etrans.
    {
      apply maponpaths_2.
      do 3 refine (poly_act_id_right _ _ _ _ _ @ _).
      refine (poly_act_id_left _ _ _ _ _ @ _).
      apply (pr1 (poly_act_functor_is_functor _ _ _ _)).
    }
    exact (poly_act_id_left P _ _ _ _).
Qed.

Definition inl_grpd_transformation
           (P Q : poly_code)
  : pstrans (⦃ P ⦄) (⦃ P + Q ⦄).
Proof.
  use make_pstrans.
  - exact (inl_grpd_transformation_data P Q).
  - exact (inl_grpd_transformation_is_pstrans P Q).
Defined.

(** Right inclusion *)
Definition inr_grpd_transformation_data_comp_data
           (P Q : poly_code)
           (G : groupoid)
  : functor_data (pr1 (⦃ Q ⦄ G)) (pr1 (⦃ P + Q ⦄ G)).
Proof.
  use make_functor_data.
  - exact inr.
  - exact (λ _ _ f, f).
Defined.

Definition inr_grpd_transformation_data_comp_is_functor
           (P Q : poly_code)
           (G : groupoid)
  : is_functor (inr_grpd_transformation_data_comp_data P Q G).
Proof.
  split.
  - intros x.
    apply idpath.
  - intros x y z f g.
    apply idpath.
Qed.

Definition inr_grpd_transformation_data_comp
           (P Q : poly_code)
           (G : groupoid)
  : pr1 (⦃ Q ⦄ G) ⟶ pr1 (⦃ P + Q ⦄ G).
Proof.
  use make_functor.
  - exact (inr_grpd_transformation_data_comp_data P Q G).
  - exact (inr_grpd_transformation_data_comp_is_functor P Q G).
Defined.

Definition inr_grpd_transformation_data_natural_data
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : nat_trans_data
      ((inr_grpd_transformation_data_comp P Q G₁)
         ∙ poly_act_functor (P + Q) _ _ F)
      ((poly_act_functor Q _ _ F)
         ∙ inr_grpd_transformation_data_comp P Q G₂)
  := λ x, poly_act_identity Q G₂ (poly_map Q F x).

Definition inr_grpd_transformation_data_natural_is_nat_trans
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : is_nat_trans _ _ (inr_grpd_transformation_data_natural_data P Q G₁ G₂ F).
Proof.
  intros x y f.
  exact (poly_act_id_right _ _ _ _ _ @ !(poly_act_id_left _ _ _ _ _)).
Qed.

Definition inr_grpd_transformation_data_natural
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : inr_grpd_transformation_data_comp P Q G₁ ∙ poly_act_functor (P + Q) _ _ F
      ⟹
      poly_act_functor Q _ _ F ∙ inr_grpd_transformation_data_comp P Q G₂.
Proof.
  use make_nat_trans.
  - exact (inr_grpd_transformation_data_natural_data P Q G₁ G₂ F).
  - exact (inr_grpd_transformation_data_natural_is_nat_trans P Q G₁ G₂ F).
Defined.
 
Definition inr_grpd_transformation_data
           (P Q : poly_code)
  : pstrans_data (⦃ Q ⦄) (⦃ P + Q ⦄).
Proof.
  use make_pstrans_data.
  - exact (inr_grpd_transformation_data_comp P Q).
  - intros G₁ G₂ F.
    use make_invertible_2cell.
    + exact (inr_grpd_transformation_data_natural P Q G₁ G₂ F).
    + apply grpd_bicat_is_invertible_2cell.
Defined.

Definition inr_grpd_transformation_is_pstrans
           (P Q : poly_code)
  : is_pstrans (inr_grpd_transformation_data P Q).
Proof.
  repeat split.
  - intros X Y f g p.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (poly_act_id_right _ _ _ _ _ @ !(poly_act_id_left _ _ _ _ _)).
  - intros X.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact ((poly_act_id_right _ _ _ _ _)
             @ !(poly_act_id_left _ _ _ _ _)
             @ !(poly_act_id_left _ _ _ _ _)
             @ poly_act_assoc _ _ _ _ _ _ _ _ _).
  - intros X Y Z f g.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    simpl.
    refine ((poly_act_id_right _ _ _ _ _)
              @ !_).
    etrans.
    {
      apply maponpaths_2.
      do 3 refine (poly_act_id_right _ _ _ _ _ @ _).
      refine (poly_act_id_left _ _ _ _ _ @ _).
      apply (pr1 (poly_act_functor_is_functor _ _ _ _)).
    }
    exact (poly_act_id_left Q _ _ _ _).
Qed.

Definition inr_grpd_transformation
           (P Q : poly_code)
  : pstrans (⦃ Q ⦄) (⦃ P + Q ⦄).
Proof.
  use make_pstrans.
  - exact (inr_grpd_transformation_data P Q).
  - exact (inr_grpd_transformation_is_pstrans P Q).
Defined.

(** Left projection *)
Definition pr1_grpd_transformation_data_comp_data
           (P Q : poly_code)
           (G : groupoid)
  : functor_data (pr1 (⦃ P * Q ⦄ G)) (pr1 (⦃ P ⦄ G)).
Proof.
  use make_functor_data.
  - exact pr1.
  - exact (λ _ _ f, pr1 f).
Defined.

Definition pr1_grpd_transformation_data_comp_is_functor
           (P Q : poly_code)
           (G : groupoid)
  : is_functor (pr1_grpd_transformation_data_comp_data P Q G).
Proof.
  split.
  - intros x.
    apply idpath.
  - intros x y z f g.
    apply idpath.
Qed.

Definition pr1_grpd_transformation_data_comp
           (P Q : poly_code)
           (G : groupoid)
  : pr1 (⦃ P * Q ⦄ G) ⟶ pr1 (⦃ P ⦄ G).
Proof.
  use make_functor.
  - exact (pr1_grpd_transformation_data_comp_data P Q G).
  - exact (pr1_grpd_transformation_data_comp_is_functor P Q G).
Defined.

Definition pr1_grpd_transformation_data_natural_data
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : nat_trans_data
      (pr1_grpd_transformation_data_comp P Q G₁ ∙ # ⦃ P ⦄ F)
      (# ⦃ P * Q ⦄ F ∙ pr1_grpd_transformation_data_comp P Q G₂)
  := λ x, poly_act_identity P G₂ (poly_map P F (pr1 x)).

Definition pr1_grpd_transformation_data_natural_is_nat_trans
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : is_nat_trans _ _ (pr1_grpd_transformation_data_natural_data P Q G₁ G₂ F).
Proof.
  intros x y f.
  exact (poly_act_id_right _ _ _ _ _ @ !(poly_act_id_left _ _ _ _ _)).
Qed.

Definition pr1_grpd_transformation_data_natural
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : (pr1_grpd_transformation_data_comp P Q G₁ ∙ # ⦃ P ⦄ F)
      ⟹
      # ⦃ P * Q ⦄ F ∙ pr1_grpd_transformation_data_comp P Q G₂.
Proof.
  use make_nat_trans.
  - exact (pr1_grpd_transformation_data_natural_data P Q G₁ G₂ F).
  - exact (pr1_grpd_transformation_data_natural_is_nat_trans P Q G₁ G₂ F).
Defined.

Definition pr1_grpd_transformation_data
           (P Q : poly_code)
  : pstrans_data (⦃ P * Q ⦄) (⦃ P ⦄).
Proof.
  use make_pstrans_data.
  - exact (pr1_grpd_transformation_data_comp P Q).
  - intros G₁ G₂ F.
    use make_invertible_2cell.
    + exact (pr1_grpd_transformation_data_natural P Q G₁ G₂ F).
    + apply grpd_bicat_is_invertible_2cell.
Defined.

Definition pr1_grpd_transformation_is_pstrans
           (P Q : poly_code)
  : is_pstrans (pr1_grpd_transformation_data P Q).
Proof.
  repeat split.
  - intros X Y f g p.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (poly_act_id_right _ _ _ _ _ @ !(poly_act_id_left _ _ _ _ _)).
  - intros X.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact ((poly_act_id_right _ _ _ _ _)
             @ !(poly_act_id_left _ _ _ _ _)
             @ !(poly_act_id_left _ _ _ _ _)
             @ poly_act_assoc _ _ _ _ _ _ _ _ _).
  - intros X Y Z f g.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    simpl.
    refine ((poly_act_id_right _ _ _ _ _)
              @ !_).
    etrans.
    {
      apply maponpaths_2.
      do 3 refine (poly_act_id_right _ _ _ _ _ @ _).
      refine (poly_act_id_left _ _ _ _ _ @ _).
      apply (pr1 (poly_act_functor_is_functor _ _ _ _)).
    }
    exact (poly_act_id_left P _ _ _ _).
Qed.

Definition pr1_grpd_transformation
           (P Q : poly_code)
  : pstrans (⦃ P * Q ⦄) (⦃ P ⦄).
Proof.
  use make_pstrans.
  - exact (pr1_grpd_transformation_data P Q).
  - exact (pr1_grpd_transformation_is_pstrans P Q).
Defined.

(** Right projection *)
Definition pr2_grpd_transformation_data_comp_data
           (P Q : poly_code)
           (G : groupoid)
  : functor_data (pr1 (⦃ P * Q ⦄ G)) (pr1 (⦃ Q ⦄ G)).
Proof.
  use make_functor_data.
  - exact pr2.
  - exact (λ _ _ f, pr2 f).
Defined.

Definition pr2_grpd_transformation_data_comp_is_functor
           (P Q : poly_code)
           (G : groupoid)
  : is_functor (pr2_grpd_transformation_data_comp_data P Q G).
Proof.
  split.
  - intros x.
    apply idpath.
  - intros x y z f g.
    apply idpath.
Qed.

Definition pr2_grpd_transformation_data_comp
           (P Q : poly_code)
           (G : groupoid)
  : pr1 (⦃ P * Q ⦄ G) ⟶ pr1 (⦃ Q ⦄ G).
Proof.
  use make_functor.
  - exact (pr2_grpd_transformation_data_comp_data P Q G).
  - exact (pr2_grpd_transformation_data_comp_is_functor P Q G).
Defined.

Definition pr2_grpd_transformation_data_natural_data
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : nat_trans_data
      (pr2_grpd_transformation_data_comp P Q G₁ ∙ # ⦃ Q ⦄ F)
      (# ⦃ P * Q ⦄ F ∙ pr2_grpd_transformation_data_comp P Q G₂)
  := λ x, poly_act_identity Q G₂ (poly_map Q F (pr2 x)).

Definition pr2_grpd_transformation_data_natural_is_nat_trans
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : is_nat_trans _ _ (pr2_grpd_transformation_data_natural_data P Q G₁ G₂ F).
Proof.
  intros x y f.
  exact (poly_act_id_right _ _ _ _ _ @ !(poly_act_id_left _ _ _ _ _)).
Qed.

Definition pr2_grpd_transformation_data_natural
           (P Q : poly_code)
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : (pr2_grpd_transformation_data_comp P Q G₁ ∙ # ⦃ Q ⦄ F)
      ⟹
      # ⦃ P * Q ⦄ F ∙ pr2_grpd_transformation_data_comp P Q G₂.
Proof.
  use make_nat_trans.
  - exact (pr2_grpd_transformation_data_natural_data P Q G₁ G₂ F).
  - exact (pr2_grpd_transformation_data_natural_is_nat_trans P Q G₁ G₂ F).
Defined.

Definition pr2_grpd_transformation_data
           (P Q : poly_code)
  : pstrans_data (⦃ P * Q ⦄) (⦃ Q ⦄).
Proof.
  use make_pstrans_data.
  - exact (pr2_grpd_transformation_data_comp P Q).
  - intros G₁ G₂ F.
    use make_invertible_2cell.
    + exact (pr2_grpd_transformation_data_natural P Q G₁ G₂ F).
    + apply grpd_bicat_is_invertible_2cell.
Defined.

Definition pr2_grpd_transformation_is_pstrans
           (P Q : poly_code)
  : is_pstrans (pr2_grpd_transformation_data P Q).
Proof.
  repeat split.
  - intros X Y f g p.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (poly_act_id_right _ _ _ _ _ @ !(poly_act_id_left _ _ _ _ _)).
  - intros X.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact ((poly_act_id_right _ _ _ _ _)
             @ !(poly_act_id_left _ _ _ _ _)
             @ !(poly_act_id_left _ _ _ _ _)
             @ poly_act_assoc _ _ _ _ _ _ _ _ _).
  - intros X Y Z f g.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    simpl.
    refine ((poly_act_id_right _ _ _ _ _)
              @ !_).
    etrans.
    {
      apply maponpaths_2.
      do 3 refine (poly_act_id_right _ _ _ _ _ @ _).
      refine (poly_act_id_left _ _ _ _ _ @ _).
      apply (pr1 (poly_act_functor_is_functor _ _ _ _)).
    }
    exact (poly_act_id_left Q _ _ _ _).
Qed.

Definition pr2_grpd_transformation
           (P Q : poly_code)
  : pstrans (⦃ P * Q ⦄) (⦃ Q ⦄).
Proof.
  use make_pstrans.
  - exact (pr2_grpd_transformation_data P Q).
  - exact (pr2_grpd_transformation_is_pstrans P Q).
Defined.

(** Needed for pairing *)
Definition pair_functor_data
           {C D₁ D₂ : category}
           (F : C ⟶ D₁)
           (G : C ⟶ D₂)
  : functor_data C (prod_category D₁ D₂).
Proof.
  use make_functor_data.
  - exact (λ x, F x ,, G x).
  - exact (λ _ _ f, #F f ,, #G f).
Defined.

Definition pair_functor_is_functor
           {C D₁ D₂ : category}
           (F : C ⟶ D₁)
           (G : C ⟶ D₂)
  : is_functor (pair_functor_data F G).
Proof.
  split.
  - intros x.
    apply pathsdirprod ; apply functor_id.
  - intros x y z f g.
    apply pathsdirprod ; apply functor_comp.
Qed.

Definition pair_functor
           {C D₁ D₂ : category}
           (F : C ⟶ D₁)
           (G : C ⟶ D₂)
  : C ⟶ prod_category D₁ D₂.
Proof.
  use make_functor.
  - exact (pair_functor_data F G).
  - exact (pair_functor_is_functor F G).
Defined.

(** Pairing of endpoints *)
Opaque ps_comp.

Section Pair.
  Context {B : bicat}
          (F : psfunctor B grpd_bicat)
          (P Q₁ Q₂ : poly_code).
  Variable (α : pstrans
                  (ps_comp ⦃ P ⦄ F)
                  (ps_comp ⦃ Q₁ ⦄ F))
           (β : pstrans
                  (ps_comp ⦃ P ⦄ F)
                  (ps_comp ⦃ Q₂ ⦄ F)).

  Definition pair_grpd_transformation_naturality_data
             (X Y : B)
             (f : X --> Y)
    : (pair_functor (α X) (β X) ∙ # ⦃ Q₁ * Q₂ ⦄ (#F f))
        ⟹
        (# ⦃ P ⦄ (#F f) ∙ pair_functor (α Y) (β Y)).
  Proof.
    use make_nat_trans.
    - exact (λ x, pr11 (psnaturality_of α f) x ,, pr11 (psnaturality_of β f) x).
    - abstract
        (intros x y g ;
         exact (pathsdirprod
                  (pr21 (psnaturality_of α f) _ _ g)
                  (pr21 (psnaturality_of β f) _ _ g))).
  Defined.
 
  Definition pair_grpd_transformation_data
    : pstrans_data
        (ps_comp ⦃ P ⦄ F)
        (ps_comp ⦃ Q₁ * Q₂ ⦄ F).
  Proof.
    use make_pstrans_data.
    - exact (λ X, pair_functor (α X) (β X)).
    - intros X Y f.
      use make_invertible_2cell.
      + exact (pair_grpd_transformation_naturality_data X Y f).
      + apply grpd_bicat_is_invertible_2cell.
  Defined.

  Definition pair_grpd_transformation_is_pstrans
    : is_pstrans pair_grpd_transformation_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      apply pathsdirprod.
      + exact (nat_trans_eq_pointwise (psnaturality_natural α X Y f g p) x).
      + exact (nat_trans_eq_pointwise (psnaturality_natural β X Y f g p) x).
    - intros X.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      apply pathsdirprod.
      + exact (nat_trans_eq_pointwise (pstrans_id α X) x).
      + exact (nat_trans_eq_pointwise (pstrans_id β X) x).
    - intros X Y Z f g.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      apply pathsdirprod.
      + exact (nat_trans_eq_pointwise (pstrans_comp α f g) x).
      + exact (nat_trans_eq_pointwise (pstrans_comp β f g) x).
  Qed.

  Definition pair_grpd_transformation
    : pstrans
        (ps_comp ⦃ P ⦄ F)
        (ps_comp ⦃ Q₁ * Q₂ ⦄ F).
  Proof.
    use make_pstrans.
    - exact pair_grpd_transformation_data.
    - exact pair_grpd_transformation_is_pstrans.
  Defined.
End Pair.

(** Constant endpoint *)
Section ConstantElement.
  Context (F : psfunctor grpd_bicat grpd_bicat)
          {T : one_type}
          (y : T).

  Definition constant_functor_data
             (G : groupoid)
    : functor_data (pr1 (F G)) (pr1 (⦃ C T ⦄ G)).
  Proof.
    use make_functor_data.
    - exact (λ _, y).
    - exact (λ _ _ _, idpath y).
  Defined.

  Definition constant_functor_is_functor
             (G : groupoid)
    : is_functor (constant_functor_data G).
  Proof.
    split ; intro ; intros ; apply idpath.
  Qed.

  Definition constant_functor
             (G : groupoid)
    : F G --> ⦃ C T ⦄ G.
  Proof.
    use make_functor.
    - exact (constant_functor_data G).
    - exact (constant_functor_is_functor G).
  Defined.

  Definition constant_el_grpd_data
    : pstrans_data F ⦃ C T ⦄.
  Proof.
    use make_pstrans_data.
    - exact (λ X, constant_functor X).
    - intros X₁ X₂ f.
      use make_invertible_2cell.
      + use make_nat_trans.
        * exact (λ _, idpath y).
        * exact (λ _ _ _, idpath _).
      + apply grpd_bicat_is_invertible_2cell.
  Defined.

  Definition constant_el_grpd_laws
    : is_pstrans constant_el_grpd_data.
  Proof.
    repeat split.
    - intros X₁ X₂ f g p.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      apply idpath.
    - intros X.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      apply idpath.
    - intros X₁ X₂ X₃ f g.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      apply idpath.
  Qed.
   
  Definition constant_el_grpd
    : pstrans F ⦃ C T ⦄.
  Proof.
    use make_pstrans.
    - exact constant_el_grpd_data.
    - exact constant_el_grpd_laws.
  Defined.
End ConstantElement.

(** Constant function endpoint *)
Section ConstantFunction.
  Context {A B : one_types}
          (ψ : A --> B).

  Definition constant_fun_grpd_data
    : pstrans_data ⦃ C A ⦄ ⦃ C B ⦄.
  Proof.
    use make_pstrans_data.
    - intro G.
      use make_functor.
      + use make_functor_data.
        * exact ψ.
        * exact (λ _ _, maponpaths ψ).
      + split.
        * intro ; apply idpath.
        * exact (λ _ _ _, maponpathscomp0 ψ).
    - intros X Y f.
      use make_invertible_2cell.
      + use make_nat_trans.
        * exact (λ _, idpath _).
        * abstract
            (intros x₁ x₂ g ;
             apply pathscomp0rid).
      + apply grpd_bicat_is_invertible_2cell.
  Defined.

  Definition constant_fun_grpd_is_pstrans
    : is_pstrans constant_fun_grpd_data.
  Proof.
    repeat split.
    - intros.
      use nat_trans_eq.
      { apply homset_property. }
      intro.
      apply idpath.
    - intros.
      use nat_trans_eq.
      { apply homset_property. }
      intro.
      apply idpath.
    - intros.
      use nat_trans_eq.
      { apply homset_property. }
      intro.
      apply idpath.
  Qed.    

  Definition constant_fun_grpd
    : pstrans ⦃ C A ⦄ ⦃ C B ⦄.
  Proof.
    use make_pstrans.
    - exact constant_fun_grpd_data.
    - exact constant_fun_grpd_is_pstrans.
  Defined.
End ConstantFunction.

(** Algebra map *)
Definition alg_map_grpd_data
           (A : poly_code)
  : pstrans_data
      (ps_comp ⦃ A ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (ps_comp ⦃ I ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
Proof.
  use make_pstrans_data.
  - exact (λ X, pr2 X).
  - intros X Y f.
    use make_invertible_2cell.
    + exact (pr12 f).
    + apply grpd_bicat_is_invertible_2cell.
Defined.

Lemma alg_map_grpd_data_is_pstrans_help_id
      (P : poly_code)
      (G : grpd_bicat)
      (x : poly_act_groupoid P G)
  : poly_act_nat_trans_data
      P G G (id₁ G) (id₁ G) (id₂ (id₁ G)) x
    =
    id₁ ((poly_act_functor P G G (id₁ G)) x).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idpath _).
  - exact (idpath _).
  - induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Qed.

Lemma alg_map_grpd_data_is_pstrans_help_comp
      (P : poly_code)
      {G₁ G₂ G₃ : grpd_bicat}
      (F₁ : G₁ --> G₂) (F₂ : G₂ --> G₃)
      x
  : poly_act_functor_composition_data
      P _ _ _ F₁ F₂ x
    · poly_act_nat_trans_data
        _ _ _ _ _
        (id₂ (F₁ · F₂)) x
    =
    poly_act_functor_composition_data
      P _ _ _ F₁ F₂ x.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idpath _).
  - exact (id_right _).
  - induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Qed.

Definition alg_map_grpd_data_is_pstrans
           (A : poly_code)
  : is_pstrans (alg_map_grpd_data A).
Proof.
  repeat split.
  - intros X Y f g α.
    use nat_trans_eq.
    { apply homset_property. }
    exact (nat_trans_eq_pointwise (pr2 α)).
  - intro X.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    assert (id₁ _ · id₁ _
                · (id₁ _ · id₁ _
                       · # (pr12 X) (poly_act_functor_identity_data A (pr1 X) x))
            =
            id₁ _ · id₁ _
                · (# (pr12 X)
                     (poly_act_functor_identity_data A (pr1 X) x
                     · poly_act_nat_trans_data
                         A _ _ _ _
                         (id₂ (id₁ (pr1 X))) x)))
      as H.
    {
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply id_left.
        }
        refine (id_left _ @ _).
        refine (assoc' _ _ _ @ _).
        refine (id_left _ @ _).
        apply id_left.
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply id_left.
        }
        apply id_left.
      }
      apply maponpaths.
      refine (_ @ id_right _).
      apply maponpaths.
      exact (alg_map_grpd_data_is_pstrans_help_id A (pr1 X) x).
    }
    exact H.
  - intros X Y Z f g.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    assert ((id₁ _)
              · id₁ _
              · ((id₁ _)
                   · # (pr11 g) (pr11 (pr2 f) x)
                   · id₁ _
                   · pr11 (pr2 g) (poly_map A (pr11 f) x)
                   · id₁ _
                   · # (pr12 Z)
                       (poly_act_functor_composition_data
                          A (pr1 X) (pr1 Y) (pr1 Z) (pr1 f) (pr1 g) x))
            =
            (id₁ _)
              · # (pr11 g) ((pr112 f) x)
              · id₁ _
              · (pr112 g) (poly_map A (pr11 f) x)
              · id₁ _
              · # (pr12 Z)
              (poly_act_functor_composition_data
                 A (pr1 X) (pr1 Y) (pr1 Z) (pr1 f) (pr1 g) x
                 · poly_act_nat_trans_data
                 A (pr1 X) (pr1 Z) (pr1 f · pr1 g) 
                 (pr1 f · pr1 g) (id₂ (pr1 f · pr1 g)) x))
      as H.
    {
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply id_left.
        }
        refine (id_left _ @ _).
        apply maponpaths_2.
        refine (id_right _ @ _).
        apply maponpaths_2.
        refine (id_right _ @ _).
        apply id_left.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (id_right _ @ _).
        apply maponpaths_2.
        refine (id_right _ @ _).
        apply id_left.
      }
      do 2 apply maponpaths.
      apply alg_map_grpd_data_is_pstrans_help_comp.
    }
    exact H.
Qed.

Definition alg_map_grpd
           (A : poly_code)
  : pstrans
      (ps_comp ⦃ A ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (ps_comp ⦃ I ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
Proof.
  use make_pstrans.
  - exact (alg_map_grpd_data A).
  - exact (alg_map_grpd_data_is_pstrans A).
Defined.

Definition sem_endpoint_grpd
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans
      (ps_comp ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (ps_comp ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T x | X Y f | ].
  - (* Identity *)
    exact (id_trans (ps_comp ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))).
  - (* Composition *)
    exact (comp_trans IHe₁ IHe₂).
  - (* Left inclusion *)
    exact (inl_grpd_transformation P Q ▻ pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)).
  - (* Right inclusion *)
    exact (inr_grpd_transformation P Q ▻ pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)).
  - (* Left projection *)
    exact (pr1_grpd_transformation P Q ▻ pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)).
  - (* Right projection *)
    exact (pr2_grpd_transformation P Q ▻ pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)).
  - (* Pairing *)
    exact (pair_grpd_transformation _ _ _ _ IHe₁ IHe₂).
  - (* Constant *)
    exact (constant_el_grpd _ x ▻ pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)).
  - (* Constant map *)
    exact (constant_fun_grpd f ▻ pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)).
  - (* Constructor *)
    exact (alg_map_grpd A).
Defined.
