(** Interpretation of endpoints in groupoid *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.

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
      (ps_comp ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)) X : groupoid)
      (ps_comp ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)) X : groupoid).
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
  : (ps_comp ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)) X : groupoid)
    ⟶
    (ps_comp ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)) X : groupoid).
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
      (ps_comp ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (ps_comp ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
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

Local Definition TODO {A : UU} : A.
Admitted.

Definition sem_endpoint_grpd_laws
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : is_pstrans (sem_endpoint_grpd_data e).
Proof.
  apply TODO.
Qed.
(*
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ]
  ; repeat split.
  - intros X Y f g α.
    use nat_trans_eq.
    { apply homset_property. }
    Transparent ps_comp.
    intro x.
    cbn.
    refine (poly_act_id_right _ @ !(poly_act_id_left _)).
    apply poly_act_id_le
    cbn.
  induction e ; repeat split.
  repeat split.
  - intros X Y f g α.
    use nat_trans_eq.
    { exact (@poly_act_isaset_mor Q (pr1 Y)). }
    intro x.
    exact (sem_endpoint_grpd_natural_natural e α x).
  - intro X.
    simpl.
    use nat_trans_eq.
    { exact (@poly_act_isaset_mor Q (pr1 X)). }
    simpl.
    cbn.
    apply TODO.
  - intros X Y Z f g.
    use nat_trans_eq.
    { exact (@poly_act_isaset_mor Q (pr1 Z)). }
    apply TODO.
    Time Qed.
 *)
Definition sem_endpoint_grpd
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans
      (ps_comp ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (ps_comp ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
Proof.
  use make_pstrans.
  - exact (sem_endpoint_grpd_data e).
  - exact (sem_endpoint_grpd_laws e).
Defined.
