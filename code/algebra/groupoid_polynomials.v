(** Interpretation of polynomials in groupoids *)
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
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.

Local Open Scope cat.

(** Action of polynomials on groupoids *)
Definition poly_act_rel
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
  : poly_act P X → poly_act P X → UU.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ a b, a = b).
  - exact (λ x y, R x y).
  - intros x y.
    induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + exact ∅.
    + exact ∅.
    + exact (IHP₂ x y).
  - exact (λ x y, IHP₁ (pr1 x) (pr1 y) × IHP₂ (pr2 x) (pr2 y)).
Defined.

Definition poly_act_rel_identity
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
           (r : ∏ (x : X), R x x)
           (x : poly_act P X)
  : poly_act_rel P R x x.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idpath x).
  - exact (r x).
  - induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (IHP₁ (pr1 x) ,, IHP₂ (pr2 x)).
Defined.

Definition poly_act_rel_inv
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
           (i : ∏ (x y : X), R x y → R y x)
           {x y : poly_act P X}
           (r : poly_act_rel P R x y)
  : poly_act_rel P R y x.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (! r).
  - exact (i _ _ r).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ _ _ r).
    + exact (fromempty r).
    + exact (fromempty r).
    + exact (IHP₂ _ _ r).
  - exact (IHP₁ _ _ (pr1 r) ,, IHP₂ _ _ (pr2 r)).
Defined.

Definition poly_act_rel_comp
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
           (c : ∏ (x y z : X), R x y → R y z → R x z)
           {x y z : poly_act P X}
           (r₁ : poly_act_rel P R x y)
           (r₂ : poly_act_rel P R y z)
  : poly_act_rel P R x z.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (r₁ @ r₂).
  - exact (c _ _ _ r₁ r₂).
  - induction x as [x | x], y as [y | y].
    + induction z as [z | z].
      * exact (IHP₁ _ _ _ r₁ r₂).
      * exact (fromempty r₂).
    + exact (fromempty r₁).
    + exact (fromempty r₁).
    + induction z as [z | z].
      * exact (fromempty r₂).
      * exact (IHP₂ _ _ _ r₁ r₂).
  - exact (IHP₁ _ _ _ (pr1 r₁) (pr1 r₂) ,, IHP₂ _ _ _ (pr2 r₁) (pr2 r₂)).
Defined.

Definition poly_act_morphism
           (P : poly_code)
           (G : groupoid)
  : poly_act P G → poly_act P G → UU
  := poly_act_rel P (@precategory_morphisms G).

Definition poly_act_identity
           {P : poly_code}
           {G : groupoid}
  : ∏ (x : poly_act P G), poly_act_morphism P G x x
  := poly_act_rel_identity P (@precategory_morphisms G) identity.

Definition poly_act_inverse
           {P : poly_code}
           {G : groupoid}
  : ∏ {x y : poly_act P G},
    poly_act_morphism P G x y → poly_act_morphism P G y x
  := @poly_act_rel_inv
       P
       _
       (@precategory_morphisms G)
       (λ _ _ f, inv_from_z_iso (make_z_iso _ _ (pr2 G _ _ f))).

Definition poly_act_compose
           {P : poly_code}
           {G : groupoid}
  : ∏ {x y z : poly_act P G},
    poly_act_morphism P G x y
    → poly_act_morphism P G y z
    → poly_act_morphism P G x z
  := @poly_act_rel_comp
       P
       _
       (@precategory_morphisms G)
       (λ _ _ _ f g, f · g).

Definition poly_act_id_right
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (f : poly_act_morphism P G x y)
  : poly_act_compose f (poly_act_identity y) = f.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply pathscomp0rid.
  - apply id_right.
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y f).
    + induction f.
    + induction f.
    + exact (IHP₂ x y f).
  - exact (pathsdirprod (IHP₁ _ _ (pr1 f)) (IHP₂ _ _ (pr2 f))).
Qed.

Definition poly_act_id_left
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (f : poly_act_morphism P G x y)
  : poly_act_compose (poly_act_identity x) f = f.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply id_left.
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y f).
    + induction f.
    + induction f.
    + exact (IHP₂ x y f).
  - exact (pathsdirprod (IHP₁ _ _ (pr1 f)) (IHP₂ _ _ (pr2 f))).
Qed.

Definition poly_act_assoc
           {P : poly_code}
           {G : groupoid}
           {w x y z : poly_act P G}
           (f : poly_act_morphism P G w x)
           (g : poly_act_morphism P G x y)
           (h : poly_act_morphism P G y z)
  : poly_act_compose f (poly_act_compose g h)
    =
    poly_act_compose (poly_act_compose f g) h.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply path_assoc.
  - apply assoc.
  - induction w as [w | w], x as [x | x].
    + induction y as [y | y].
      * induction z as [z | z].
        ** exact (IHP₁ w x y z f g h).
        ** induction h.
      * induction g.
    + induction f.
    + induction f.
    + induction y as [y | y].
      * induction g.
      * induction z as [z | z].
        ** induction h.
        ** exact (IHP₂ w x y z f g h).
  - exact (pathsdirprod
             (IHP₁ _ _ _ _ (pr1 f) (pr1 g) (pr1 h))
             (IHP₂ _ _ _ _ (pr2 f) (pr2 g) (pr2 h))).
Qed.

Definition poly_act_inv_right
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (f : poly_act_morphism P G x y)
  : poly_act_compose f (poly_act_inverse f)
    =
    poly_act_identity x.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply pathsinv0r.
  - exact (z_iso_inv_after_z_iso (make_z_iso f _ (pr2 G x y f))).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y f).
    + induction f.
    + induction f.
    + exact (IHP₂ x y f).
  - exact (pathsdirprod (IHP₁ _ _ (pr1 f)) (IHP₂ _ _ (pr2 f))).
Qed.

Definition poly_act_inv_left
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (f : poly_act_morphism P G x y)
  : poly_act_compose (poly_act_inverse f) f
    =
    poly_act_identity y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply pathsinv0l.
  - exact (z_iso_after_z_iso_inv (make_z_iso f _ (pr2 G x y f))).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y f).
    + induction f.
    + induction f.
    + exact (IHP₂ x y f).
  - exact (pathsdirprod (IHP₁ _ _ (pr1 f)) (IHP₂ _ _ (pr2 f))).
Qed.

Definition poly_act_isaset_mor
           {P : poly_code}
           {G : groupoid}
  : ∏ (x y : poly_act P G), isaset (poly_act_morphism P G x y).
Proof.
  intros x y.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (one_type_isofhlevel A x y).
  - exact (homset_property G x y).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + exact isasetempty.
    + exact isasetempty.
    + exact (IHP₂ x y).
  - exact (isasetdirprod _ _ (IHP₁ (pr1 x) (pr1 y)) (IHP₂ (pr2 x) (pr2 y))).
Qed.

Definition poly_act_groupoid
           (P : poly_code)
           (G : groupoid)
  : groupoid.
Proof.
  use make_grpd_bicat.
  - exact (poly_act P (pr1 G)).
  - exact (poly_act_morphism P G).
  - exact (@poly_act_identity P G).
  - exact (@poly_act_inverse P G).
  - exact (@poly_act_compose P G).
  - exact (@poly_act_id_right P G).
  - exact (@poly_act_id_left P G).
  - exact (@poly_act_assoc P G).
  - exact (@poly_act_inv_right P G).
  - exact (@poly_act_inv_left P G).
  - exact (@poly_act_isaset_mor P G).
Defined.

(** Action of polynomials on functors *)
Definition poly_act_functor_morphisms
           (P : poly_code)
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
           {x y : poly_act P G₁}
  : poly_act_morphism P G₁ x y
    →
    poly_act_morphism P G₂ (poly_map P F x) (poly_map P F y).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ p, p).
  - exact (λ f, #F f).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + exact fromempty.
    + exact fromempty.
    + exact (IHP₂ x y).
  - exact (λ f, IHP₁ _ _ (pr1 f) ,, IHP₂ _ _ (pr2 f)).
Defined.

Definition poly_act_functor_data
           (P : poly_code)
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
  : functor_data (poly_act_groupoid P G₁) (poly_act_groupoid P G₂).
Proof.
  use make_functor_data.
  - exact (poly_map P F).
  - exact (@poly_act_functor_morphisms P _ _ F).
Defined.

Definition poly_act_functor_is_functor
           (P : poly_code)
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
  : is_functor (poly_act_functor_data P F).
Proof.
  split.
  - intros x.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    + exact (idpath _).
    + exact (functor_id F x).
    + induction x as [x | x].
      * exact (IHP₁ x).
      * exact (IHP₂ x).
    + exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
  - intros x y z.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    + exact (λ f g, idpath _).
    + exact (functor_comp F).
    + induction x as [x | x], y as [y | y].
      * induction z as [z | z].
        ** exact (IHP₁ x y z).
        ** intros f g ; induction g.
      * intro f ; induction f.
      * intro f ; induction f.
      * induction z as [z | z].
        ** intros f g ; induction g.
        ** exact (IHP₂ x y z).
    + exact (λ f g, pathsdirprod
                      (IHP₁ _ _ _ (pr1 f) (pr1 g))
                      (IHP₂ _ _ _ (pr2 f) (pr2 g))).
Qed.    

Definition poly_act_functor
           (P : poly_code)
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
  : poly_act_groupoid P G₁ ⟶ poly_act_groupoid P G₂.
Proof.
  use make_functor.
  - exact (@poly_act_functor_data P G₁ G₂ F).
  - exact (@poly_act_functor_is_functor P G₁ G₂ F).
Defined.

(** Action of polynomials on natural transformations *)
Definition poly_act_nat_trans_data_help
           (P : poly_code)
           {X : UU} {G : groupoid}
           {f g : X → G}
           (α : ∏ (x : X), G ⟦ f x , g x ⟧)
  : ∏ (x : poly_act P X),
    poly_act_morphism P G (poly_map P f x) (poly_map P g x).
Proof.
  intro x.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idpath x).
  - exact (α x).
  - induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (IHP₁ (pr1 x) ,, IHP₂ (pr2 x)).
Defined.

Definition poly_act_nat_trans_data
           (P : poly_code)
           {G₁ G₂ : groupoid}
           {F₁ F₂ : G₁ ⟶ G₂}
           (α : F₁ ⟹ F₂)
  : nat_trans_data (poly_act_functor P F₁) (poly_act_functor P F₂).
Proof.
  exact (poly_act_nat_trans_data_help P α).
Defined.

Definition poly_act_nat_trans_is_nat_trans
           (P : poly_code)
           {G₁ G₂ : groupoid}
           {F₁ F₂ : G₁ ⟶ G₂}
           (α : F₁ ⟹ F₂)
  : is_nat_trans _ _ (poly_act_nat_trans_data P α).
Proof.
  intros x y.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact pathscomp0rid.
  - exact (λ f, pr2 α _ _ f).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + intro f ; induction f.
    + intro f ; induction f.
    + exact (IHP₂ x y).
  - exact (λ f, pathsdirprod (IHP₁ _ _ (pr1 f)) (IHP₂ _ _ (pr2 f))).
Qed.

Definition poly_act_nat_trans
           (P : poly_code)
           {G₁ G₂ : groupoid}
           {F₁ F₂ : G₁ ⟶ G₂}
           (α : F₁ ⟹ F₂)
  : poly_act_functor P F₁ ⟹ poly_act_functor P F₂.
Proof.
  use make_nat_trans.
  - exact (poly_act_nat_trans_data P α).
  - exact (poly_act_nat_trans_is_nat_trans P α).
Defined.

(** Action on identity *)
Definition poly_act_functor_identity_data
           (P : poly_code)
           (G : groupoid)
  : nat_trans_data
      (functor_identity (poly_act_groupoid P G))
      (poly_act_functor P (functor_identity G)).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact idpath.
  - exact identity.
  - intro x ; induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (λ x, IHP₁ (pr1 x) ,, IHP₂ (pr2 x)).
Defined.

Definition poly_act_functor_identity_is_nat_trans
           (P : poly_code)
           (G : groupoid)
  : is_nat_trans _ _ (poly_act_functor_identity_data P G).
Proof.
  intros x y.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact pathscomp0rid.
  - exact (λ f, id_right f @ !(id_left f)).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + intro f ; induction f.
    + intro f ; induction f.
    + exact (IHP₂ x y).
  - exact (λ f, pathsdirprod (IHP₁ _ _ (pr1 f)) (IHP₂ _ _ (pr2 f))).
Qed.

Definition poly_act_functor_identity
           (P : poly_code)
           (G : groupoid)
  : (functor_identity (poly_act_groupoid P G))
      ⟹
      poly_act_functor P (functor_identity G).
Proof.
  use make_nat_trans.
  - exact (poly_act_functor_identity_data P G).
  - exact (poly_act_functor_identity_is_nat_trans P G).
Defined.

(** Action on composition *)
Definition poly_act_functor_composition_data
           (P : poly_code)
           {G₁ G₂ G₃ : groupoid}
           (F₁ : G₁ ⟶ G₂) (F₂ : G₂ ⟶ G₃)
  : nat_trans_data
      (poly_act_functor P F₁ ∙ poly_act_functor P F₂)
      (poly_act_functor P (F₁ ∙ F₂)).
Proof.
  intro x.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idpath x).
  - exact (identity _).
  - induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (IHP₁ (pr1 x) ,, IHP₂ (pr2 x)).
Defined.

Definition poly_act_functor_composition_is_nat_trans
           (P : poly_code)
           {G₁ G₂ G₃ : groupoid}
           (F₁ : G₁ ⟶ G₂) (F₂ : G₂ ⟶ G₃)
  : is_nat_trans _ _ (poly_act_functor_composition_data P F₁ F₂).
Proof.
  intros x y.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact pathscomp0rid.
  - exact (λ f, id_right _ @ !(id_left _)).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + intro f ; induction f.
    + intro f ; induction f.
    + exact (IHP₂ x y).
  - exact (λ f, pathsdirprod (IHP₁ _ _ (pr1 f)) (IHP₂ _ _ (pr2 f))).
Qed.
  
Definition poly_act_functor_composition
           (P : poly_code)
           {G₁ G₂ G₃ : groupoid}
           (F₁ : G₁ ⟶ G₂) (F₂ : G₂ ⟶ G₃)
  : (poly_act_functor P F₁ ∙ poly_act_functor P F₂)
      ⟹
      poly_act_functor P (F₁ ∙ F₂).
Proof.
  use make_nat_trans.
  - exact (poly_act_functor_composition_data P F₁ F₂).
  - exact (poly_act_functor_composition_is_nat_trans P F₁ F₂).
Defined.

(** Putting it all together *)
Definition sem_poly_grpd_data
           (P : poly_code)
  : psfunctor_data grpd_bicat grpd_bicat.
Proof.
  use make_psfunctor_data.
  - exact (poly_act_groupoid P).
  - exact (@poly_act_functor P).
  - exact (@poly_act_nat_trans P).
  - exact (@poly_act_functor_identity P).
  - exact (@poly_act_functor_composition P).
Defined.

Definition sem_poly_grpd_laws
           (P : poly_code)
  : psfunctor_laws (sem_poly_grpd_data P).
Proof.
  repeat split ; induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    induction x as [x | x].
    + exact (nat_trans_eq_pointwise (IHP₁ _ _ _) x).
    + exact (nat_trans_eq_pointwise (IHP₂ _ _ _) x).
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (pathsdirprod
              (nat_trans_eq_pointwise (IHP₁ _ _ _) (pr1 x))
              (nat_trans_eq_pointwise (IHP₂ _ _ _) (pr2 x))).
  - intros G₁ G₂ F₁ F₂ F₃ α β.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ F₁ F₂ F₃ α β.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ F₁ F₂ F₃ α β.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    induction x as [x | x].
    + exact (nat_trans_eq_pointwise (IHP₁ _ _ _ _ _ _ _) x).
    + exact (nat_trans_eq_pointwise (IHP₂ _ _ _ _ _ _ _) x).
  - intros G₁ G₂ F₁ F₂ F₃ α β.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (pathsdirprod
             (nat_trans_eq_pointwise (IHP₁ _ _ _ _ _ _ _) (pr1 x))
             (nat_trans_eq_pointwise (IHP₂ _ _ _ _ _ _ _) (pr2 x))).
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    refine (!_).
    exact (id_right _ @ id_right _ @ functor_id _ _).
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    induction x as [x | x].
    + exact (nat_trans_eq_pointwise (IHP₁ _ _ _) x).
    + exact (nat_trans_eq_pointwise (IHP₂ _ _ _) x).
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (pathsdirprod
             (nat_trans_eq_pointwise (IHP₁ _ _ _) (pr1 x))
             (nat_trans_eq_pointwise (IHP₂ _ _ _) (pr2 x))).
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    refine (!_).
    exact (id_right _ @ id_right _).
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    induction x as [x | x].
    + exact (nat_trans_eq_pointwise (IHP₁ _ _ _) x).
    + exact (nat_trans_eq_pointwise (IHP₂ _ _ _) x).
  - intros G₁ G₂ F.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (pathsdirprod
             (nat_trans_eq_pointwise (IHP₁ _ _ _) (pr1 x))
             (nat_trans_eq_pointwise (IHP₂ _ _ _) (pr2 x))).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ F₄.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ G₃ F₁ F₂ F₃ F₄.
    use nat_trans_eq.
    { apply homset_property. }
    intro ; cbn.
    exact (id_right _ @ id_right _ @ !(id_right _ @ id_left _ @ functor_id _ _)).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ F₄.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    induction x as [x | x].
    + exact (nat_trans_eq_pointwise (IHP₁ _ _ _ _ _ _ _) x).
    + exact (nat_trans_eq_pointwise (IHP₂ _ _ _ _ _ _ _) x).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ F₄.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (pathsdirprod
             (nat_trans_eq_pointwise (IHP₁ _ _ _ _ _ _ _) (pr1 x))
             (nat_trans_eq_pointwise (IHP₂ _ _ _ _ _ _ _) (pr2 x))).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    exact (id_left _ @ !(id_right _)).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    induction x as [x | x].
    + exact (nat_trans_eq_pointwise (IHP₁ _ _ _ _ _ _ _) x).
    + exact (nat_trans_eq_pointwise (IHP₂ _ _ _ _ _ _ _) x).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (pathsdirprod
             (nat_trans_eq_pointwise (IHP₁ _ _ _ _ _ _ _) (pr1 x))
             (nat_trans_eq_pointwise (IHP₂ _ _ _ _ _ _ _) (pr2 x))).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ F₄.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    apply idpath.
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α.
    use nat_trans_eq.
    { apply homset_property. }
    intro.
    exact (id_left _ @ !(id_right _)).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    induction x as [x | x].
    + exact (nat_trans_eq_pointwise (IHP₁ _ _ _ _ _ _ _) x).
    + exact (nat_trans_eq_pointwise (IHP₂ _ _ _ _ _ _ _) x).
  - intros G₁ G₂ G₃ F₁ F₂ F₃ α.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (pathsdirprod
             (nat_trans_eq_pointwise (IHP₁ _ _ _ _ _ _ _) (pr1 x))
             (nat_trans_eq_pointwise (IHP₂ _ _ _ _ _ _ _) (pr2 x))).  
Qed.

Definition sem_poly_grpd
           (P : poly_code)
  : psfunctor grpd_bicat grpd_bicat.
Proof.
  use make_psfunctor.
  - exact (sem_poly_grpd_data P).
  - exact (sem_poly_grpd_laws P).
  - split ; intros ; apply grpd_bicat_is_invertible_2cell.
Defined.

Notation "⦃ P ⦄" := (sem_poly_grpd P).
