(** Interpretation of endpoints in groupoid *)
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

Local Open Scope cat.

Definition sem_endpoint_grpd_data_functor_morphism
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : groupoid}
           (cX : (⦃ A ⦄ X : groupoid) ⟶ (X : groupoid))
           {x y : poly_act P X}
  : poly_act_morphism
      P X
      x y
    →
    poly_act_morphism
      Q X
      (sem_endpoint_UU e (λ z, cX z) x)
      (sem_endpoint_UU e (λ z, cX z) y).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ g | ].
  - (* Identity *)
    exact (λ f, f).
  - (* Composition *)
    exact (λ f, IHe₂ _ _ (IHe₁ _ _ f)).
  - (* Left inclusion *)
    exact (λ f, f).
  - (* Right inclusion *)
    exact (λ f, f).
  - (* Left projection *)
    exact pr1.
  - (* Right projection *)
    exact pr2.
  - (* Pairing *)
    exact (λ f, IHe₁ _ _ f ,, IHe₂ _ _ f).
  - (* Constant *)
    exact (λ _, idpath _).
  - (* Constant map *)
    exact (maponpaths g).
  - (* Constructor *)
    exact (#cX).
Defined.

Definition sem_endpoint_grpd_data_functor_data
           {A P Q : poly_code}
           (e : endpoint A P Q)
           (X : total_bicat (disp_alg_bicat ⦃ A ⦄))
  : functor_data
      (comp_psfunctor ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)) X : groupoid)
      (comp_psfunctor ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)) X : groupoid).
Proof.
  use make_functor_data.
  - exact (sem_endpoint_UU e (λ z, (pr2 X : _ ⟶ _) z)).
  - exact (λ _ _ f, sem_endpoint_grpd_data_functor_morphism e (pr2 X) f).
Defined.

Definition sem_endpoint_grpd_data_functor_idax
           {A P Q : poly_code}
           (e : endpoint A P Q)
           (X : total_bicat (disp_alg_bicat ⦃ A ⦄))
  : functor_idax (sem_endpoint_grpd_data_functor_data e X).
Proof.
  intro x ; cbn.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ g | ].
  - (* Identity *)
    apply idpath.
  - (* Composition *)
    exact (maponpaths (sem_endpoint_grpd_data_functor_morphism e₂ (pr2 X)) (IHe₁ _)
           @ IHe₂ _).
  - (* Left inclusion *)
    apply idpath.
  - (* Right inclusion *)
    apply idpath.
  - (* Left projection *)
    apply idpath.
  - (* Right projection *)
    apply idpath.
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    apply (functor_id (pr2 X)).
Qed.

Definition sem_endpoint_grpd_data_functor_compax
           {A P Q : poly_code}
           (e : endpoint A P Q)
           (X : total_bicat (disp_alg_bicat ⦃ A ⦄))
  : functor_compax (sem_endpoint_grpd_data_functor_data e X).
Proof.
  intros x y z f g ; cbn.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    apply idpath.
  - (* Composition *)
    exact (maponpaths
             (sem_endpoint_grpd_data_functor_morphism e₂ (pr2 X))
             (IHe₁ _ _ _ _ _)
           @ IHe₂ _ _ _ _ _).
  - (* Left inclusion *)
    apply idpath.
  - (* Right inclusion *)
    apply idpath.
  - (* Left projection *)
    apply idpath.
  - (* Right projection *)
    apply idpath.
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ _ _ _ f g) (IHe₂ _ _ _ f g)).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    apply maponpathscomp0.
  - (* Constructor *)
    apply (functor_comp (pr2 X)).
Qed.

Definition sem_endpoint_grpd_data_functor_laws
           {A P Q : poly_code}
           (e : endpoint A P Q)
           (X : total_bicat (disp_alg_bicat ⦃ A ⦄))
  : is_functor (sem_endpoint_grpd_data_functor_data e X).
Proof.
  split.
  - exact (sem_endpoint_grpd_data_functor_idax e X).
  - exact (sem_endpoint_grpd_data_functor_compax e X).
Qed.

Definition sem_endpoint_grpd_data_functor
           {A P Q : poly_code}
           (e : endpoint A P Q)
           (X : total_bicat (disp_alg_bicat ⦃ A ⦄))
  : (comp_psfunctor ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)) X : groupoid)
    ⟶
    (comp_psfunctor ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)) X : groupoid).
Proof.
  use make_functor.
  - exact (sem_endpoint_grpd_data_functor_data e X).
  - exact (sem_endpoint_grpd_data_functor_laws e X).
Defined.

Definition sem_endpoint_grpd_natural_data
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (f : X --> Y)
  : nat_trans_data
      (functor_composite_data
         (sem_endpoint_grpd_data_functor_data e X)
         (poly_act_functor_data Q (pr1 f)))
      (functor_composite_data
         (poly_act_functor_data P (pr1 f))
         (sem_endpoint_grpd_data_functor_data e Y)).
Proof.
  intros x ; cbn in x ; cbn.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ g | ].
  - (* Identity *)
    apply poly_act_identity.
  - (* Composition *)
    exact (poly_act_compose
             (IHe₂ _)
             (#(sem_endpoint_grpd_data_functor e₂ Y) (IHe₁ x))).
  - (* Left inclusion *)
    apply poly_act_identity.
  - (* Right inclusion *)
    apply poly_act_identity.
  - (* Left projection *)
    apply poly_act_identity.
  - (* Right projection *)
    apply poly_act_identity.
  - (* Pairing *)
    exact (IHe₁ x ,, IHe₂ x).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    exact (pr112 f x).
Defined.

Definition sem_endpoint_grpd_natural_laws
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (f : X --> Y)
  : is_nat_trans
      _ _
      (sem_endpoint_grpd_natural_data e f).
Proof.
  intros x y g ; cbn.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Composition *)
    simpl.
    specialize (IHe₁ _ _ g).
    specialize (IHe₂ _ _ (sem_endpoint_grpd_data_functor_morphism e₁ (pr2 X) g)).
    etrans.
    {
      apply poly_act_assoc.
    }
    etrans.
    {
      apply maponpaths_2.
      exact IHe₂.
    }
    etrans.
    {
      exact (!(poly_act_assoc _ _ _)).
    }
    refine (_ @ poly_act_assoc _ _ _).
    apply maponpaths.
    pose (@functor_comp _ _ (sem_endpoint_grpd_data_functor e₂ Y)) as p.
    cbn in p.
    rewrite <- !p.
    apply maponpaths.
    exact IHe₁.
  - (* Left inclusion *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Right inclusion *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Left projection *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Right projection *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ _ _ g) (IHe₂ _ _ g)).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    apply pathscomp0rid.
  - (* Constructor *)
    exact (pr212 f _ _ g).
Qed.

Definition sem_endpoint_grpd_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (f : X --> Y)
  : functor_composite_data
      (sem_endpoint_grpd_data_functor_data e X)
      (poly_act_functor_data Q (pr1 f))
    ⟹
    functor_composite_data
      (poly_act_functor_data P (pr1 f))
      (sem_endpoint_grpd_data_functor_data e Y).
Proof.
  use make_nat_trans.
  - exact (sem_endpoint_grpd_natural_data e f).
  - exact (sem_endpoint_grpd_natural_laws e f).
Defined.

Definition sem_endpoint_grpd_data
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans_data
      (comp_psfunctor ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (comp_psfunctor ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
Proof.
  use make_pstrans_data.
  - exact (sem_endpoint_grpd_data_functor e).
  - intros X Y f.
    use make_invertible_2cell.
    + exact (sem_endpoint_grpd_natural e f).
    + apply grpd_bicat_is_invertible_2cell.
Defined.

Definition sem_endpoint_grpd_natural_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           {f g : X --> Y}
           (α : f ==> g)
           (z : poly_act P (pr11 X))
  : poly_act_compose
      (poly_act_nat_trans_data
         Q (pr1 α)
         (sem_endpoint_UU e (λ z0, (pr12 X) z0) z))
      (sem_endpoint_grpd_natural_data e g z)
    =
    poly_act_compose
      (sem_endpoint_grpd_natural_data e f z)
      (sem_endpoint_grpd_data_functor_morphism
         e (pr2 Y)
         (poly_act_nat_trans_data P (pr1 α) z)).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Composition *)
    simpl.
    etrans.
    {
      apply poly_act_assoc.
    }
    etrans.
    {
      apply maponpaths_2.
      apply IHe₂.
    }
    etrans.
    {
      exact (!(poly_act_assoc _ _ _)).
    }
    refine (_ @ poly_act_assoc _ _ _).
    apply maponpaths.
    pose (@functor_comp _ _ (sem_endpoint_grpd_data_functor e₂ Y)) as p.
    cbn in p.
    rewrite <- !p.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(IHe₁ _)).
    }
    rewrite p.
    apply idpath.
  - (* Left inclusion *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Right inclusion *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Left projection *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Right projection *)
    simpl.
    rewrite poly_act_id_left, poly_act_id_right.
    apply idpath.
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ z) (IHe₂ z)).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    exact (nat_trans_eq_pointwise (pr2 α) z).
Qed.

Definition sem_endpoint_grpd_id_constr
           {P : poly_code}
           {X : groupoid}
           (z : poly_act P (pr11 X))
           (f : poly_act_morphism P X z _)
  : f
    =
    poly_act_compose
      f
      (poly_act_nat_trans_data
         P
         (nat_trans_id (functor_identity X)) z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (!(pathscomp0rid _)).
  - exact (!(id_right _)).
  - induction z as [z | z].
    + apply IHP₁.
    + apply IHP₂.
  - exact (pathsdirprod (IHP₁ _ _) (IHP₂ _ _)).
Qed.

Definition sem_endpoint_grpd_id
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (z : poly_act P (pr11 X))
  : poly_act_functor_identity_data Q (pr1 X)
    (sem_endpoint_UU e (pr12 X) z)
  · poly_act_nat_trans_data Q (id₂ (id₁ (pr1 X)))
      (sem_endpoint_UU e (pr12 X) z)
  · sem_endpoint_grpd_natural_data e (id₁ X) z
  =
  sem_endpoint_grpd_data_functor_morphism
    e
    (pr2 X)
    (poly_act_functor_identity_data P (pr1 X) z
     · poly_act_nat_trans_data P (id₂ (id₁ (pr1 X))) z).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    apply poly_act_id_right.
  - (* Composition *)
    refine (poly_act_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply IHe₂.
    }
    etrans.
    {
      refine (!_).
      exact (functor_comp
               (sem_endpoint_grpd_data_functor e₂ _)
               _
               _).
    }
    exact (maponpaths
             (sem_endpoint_grpd_data_functor_morphism e₂ (pr2 X))
             (IHe₁ _)).
  - (* Left inclusion *)
    apply (@poly_act_id_right P).
  - (* Right inclusion *)
    apply (@poly_act_id_right Q).
  - (* Left projection *)
    apply (@poly_act_id_right P).
  - (* Right projection *)
    apply (@poly_act_id_right Q).
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ _) (IHe₂ _)).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).
      apply id_left.
    }
    etrans.
    {
      apply id_left.
    }
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).      
      exact (@id_left (pr11 X) _ _ _).
    }
    etrans.
    {
      exact (@id_left (pr11 X) _ _ _).
    }
    refine (maponpaths (#(pr12 X)) _).
    exact (sem_endpoint_grpd_id_constr z _).
Qed.

Definition sem_endpoint_grpd_comp_constr
           {P : poly_code}
           {X Y Z : groupoid}
           (f : X ⟶ Y)
           (g : Y ⟶ Z)
           (z : poly_act P (pr11 X))
  : poly_act_functor_composition_data P f g z
    =
    poly_act_compose
      (poly_act_functor_composition_data P f g z)
      (poly_act_nat_trans_data P (nat_trans_id (functor_composite f g)) z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (!(pathscomp0rid _)).
  - exact (!(id_right _)).
  - induction z as [z | z].
    + apply IHP₁.
    + apply IHP₂.
  - exact (pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition sem_endpoint_grpd_comp
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y Z : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (f : total_bicat (disp_alg_bicat ⦃ A ⦄) ⟦ X, Y ⟧)
           (g : total_bicat (disp_alg_bicat ⦃ A ⦄) ⟦ Y, Z ⟧)
           (z : poly_act P (pr11 X))
  : poly_act_functor_composition_data
      Q (pr1 f) (pr1 g)
      (sem_endpoint_UU e (pr12 X) z)
  · poly_act_nat_trans_data
      Q (id₂ (pr1 f · pr1 g))
      (sem_endpoint_UU e (pr12 X) z)
  · sem_endpoint_grpd_natural_data e (f · g) z
  =
  poly_act_compose
    (poly_act_functor_morphisms Q (pr1 g) (sem_endpoint_grpd_natural_data e f z))
    (poly_act_compose
       (sem_endpoint_grpd_natural_data e g (poly_map P (pr11 f) z))
       (sem_endpoint_grpd_data_functor_morphism
          e (pr2 Z)
          (poly_act_functor_composition_data P (pr1 f) (pr1 g) z
           · poly_act_nat_trans_data P (id₂ (pr1 f · pr1 g)) z))).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    refine (poly_act_id_right _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (functor_id (poly_act_functor P (pr1 g))).
    }
    etrans.
    {
      apply poly_act_id_left.
    }
    apply poly_act_id_left.
  - (* Composition *)
    refine (poly_act_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply IHe₂.
    }
    clear IHe₂.
    refine (!(poly_act_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!(poly_act_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply (functor_comp (sem_endpoint_grpd_data_functor e₂ Z)).
      }
      apply maponpaths.
      apply IHe₁.
    }
    clear IHe₁.
    etrans.
    {
      do 2 apply maponpaths.
      apply (functor_comp (sem_endpoint_grpd_data_functor e₂ Z)).
    }
    refine (!_).
    refine (poly_act_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (poly_act_assoc _ _ _ @ _).
      do 2 apply maponpaths_2.
      apply (functor_comp (poly_act_functor R (pr1 g))).
    }
    do 3 refine (!(poly_act_assoc _ _ _) @ _).
    apply maponpaths.
    refine (poly_act_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.     
      apply (nat_trans_ax (sem_endpoint_grpd_natural e₂ g)).
    }
    refine (!(poly_act_assoc _ _ _) @ _).
    do 2 apply maponpaths.
    refine (!_).
    apply (functor_comp (sem_endpoint_grpd_data_functor e₂ Z)).
  - (* Left inclusion *)
    refine (poly_act_id_right _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (functor_id (poly_act_functor P (pr1 g))).
    }
    etrans.
    {
      apply (@poly_act_id_left P).
    }
    apply poly_act_id_left.
  - (* Right inclusion *)
    refine (poly_act_id_right _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (functor_id (poly_act_functor Q (pr1 g))).
    }
    etrans.
    {
      apply (@poly_act_id_left Q).
    }
    apply poly_act_id_left.
  - (* Left projection *)
    refine (poly_act_id_right _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (functor_id (poly_act_functor P (pr1 g))).
    }
    etrans.
    {
      apply poly_act_id_left.
    }
    apply poly_act_id_left.
  - (* Right projection *)
    refine (poly_act_id_right _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (functor_id (poly_act_functor Q (pr1 g))).
    }
    etrans.
    {
      apply poly_act_id_left.
    }
    apply poly_act_id_left.
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ _) (IHe₂ _)).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).
      apply id_left.
    }
    refine (id_left _ @ _).
    etrans.
    {
      refine (maponpaths (λ z, z · _) (id_right _ @ _)).
      refine (maponpaths (λ z, z · _) (id_right _ @ _)).
      exact (id_left (# (pr11 g) _)).
    }
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (λ z, # (pr11 g) _ · z) _).
    refine (maponpaths (λ z, _ · z) _).
    refine (maponpaths (# (pr12 Z)) _).
    exact (sem_endpoint_grpd_comp_constr (pr1 f) (pr1 g) z).
Qed.
 
Opaque comp_psfunctor.

Definition sem_endpoint_grpd_laws
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : is_pstrans (sem_endpoint_grpd_data e).
Proof.
  repeat split
  ; [intros X Y f g α | intro X | intros X Y Z f g].
  - use nat_trans_eq
    ; [ exact (@poly_act_isaset_mor _ _) | intro z].
    exact (sem_endpoint_grpd_natural_natural e α z).
  - use nat_trans_eq
    ; [ exact (@poly_act_isaset_mor _ _) | intro z].
    refine (sem_endpoint_grpd_id e z @ _).
    refine (!_).
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).
      apply id_left.
    }
    apply id_left.
  - use nat_trans_eq
    ; [ exact (@poly_act_isaset_mor _ _) | intro z].
    refine (sem_endpoint_grpd_comp e f g z @ _).
    refine (!_).
    etrans.
    {
      refine (maponpaths
                (λ q, poly_act_compose
                        q
                        _)
                _).
      etrans.
      {
        exact (@poly_act_id_right
                 Q (pr1 Z)
                 _ _
                 (poly_act_compose
                    _
                    _)).
      }
      refine (maponpaths
                (λ q, poly_act_compose
                        q
                        _)
                _).
      etrans.
      {
        exact (@poly_act_id_right
                 Q (pr1 Z)
                 _ _
                 (poly_act_compose
                    _
                    _)).
      }
      exact (@poly_act_id_left Q (pr1 Z) _ _ _).
    }
    refine (!_).
    apply poly_act_assoc.
Qed.    

Definition sem_endpoint_grpd
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans
      (comp_psfunctor ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (comp_psfunctor ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
Proof.
  use make_pstrans.
  - exact (sem_endpoint_grpd_data e).
  - exact (sem_endpoint_grpd_laws e).
Defined.
