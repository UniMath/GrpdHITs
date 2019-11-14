(** Here we define the notion of a HIT *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

Definition quot_rel
           {X : UU}
           (R : X → X → UU)
           (ER : ∏ (x y : X), R x y → R x y → hProp)
  : X → X → hSet
  := λ x y,
     make_hSet
       (setquot (ER x y))
       (isasetsetquot _).

Definition poly_act_rel2
           (P : poly_code)
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), R x y → R x y → UU)
           {x y : poly_act P X}
  : poly_act_rel P R x y → poly_act_rel P R x y → UU.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ p q, p = q).
  - exact (ER x y).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + exact (λ _ _, hfalse).
    + exact (λ _ _, hfalse).
    + exact (IHP₂ x y).
  - exact (λ r₁ r₂, IHP₁ _ _ (pr1 r₁) (pr1 r₂) × IHP₂ _ _ (pr2 r₁) (pr2 r₂)).
Defined.

Definition isaprop_poly_act_rel2
           (P : poly_code)
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), R x y → R x y → hProp)
           {x y : poly_act P X}
           (r₁ r₂ : poly_act_rel P R x y)
  : isaprop (poly_act_rel2 P ER r₁ r₂).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (one_type_isofhlevel A _ _ _ _).
  - apply (ER x y r₁ r₂).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y r₁ r₂).
    + apply isapropempty.
    + apply isapropempty.
    + exact (IHP₂ x y r₁ r₂).
  - exact (isapropdirprod
             _ _
             (IHP₁ _ _ (pr1 r₁) (pr1 r₂))
             (IHP₂ _ _ (pr2 r₁) (pr2 r₂))).
Defined.

Definition poly_act_hrel
           (P : poly_code)
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), hrel (R x y))
           (x y : poly_act P X)
  : hrel (poly_act_rel P R x y)
  := λ r₁ r₂,
     make_hProp
       (poly_act_rel2 P ER r₁ r₂)
       (isaprop_poly_act_rel2 P ER r₁ r₂).

Definition poly_act_hrel_istrans
           (P : poly_code)
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), hrel (R x y))
           (HER : ∏ (x y : X), istrans (ER x y))
           (x y : poly_act P X)
  : istrans (poly_act_hrel P ER x y).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ _ _ _ p q, p @ q).
  - exact (HER x y).
  - intros r₁ r₂ r₃ p q.
    induction x as [x | x], y as [y | y].
    + exact (IHP₁ _ _ _ _ _ p q).
    + exact (fromempty p).
    + exact (fromempty p).
    + exact (IHP₂ _ _ _ _ _ p q).
  - intros r₁ r₂ r₃ p q.
    exact (IHP₁ _ _ _ _ _ (pr1 p) (pr1 q) ,, IHP₂ _ _ _ _ _ (pr2 p) (pr2 q)).
Qed.

Definition poly_act_hrel_isrefl
           (P : poly_code)
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), hrel (R x y))
           (HER : ∏ (x y : X), isrefl (ER x y))
           (x y : poly_act P X)
  : isrefl (poly_act_hrel P ER x y).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ _, idpath _).
  - exact (HER x y).
  - intros r.
    induction x as [x | x], y as [y | y].
    + exact (IHP₁ _ _ r).
    + exact (fromempty r).
    + exact (fromempty r).
    + exact (IHP₂ _ _ r).
  - intros r.
    exact (IHP₁ _ _ (pr1 r) ,, IHP₂ _ _ (pr2 r)).
Qed.

Definition poly_act_hrel_issymm
           (P : poly_code)
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), hrel (R x y))
           (HER : ∏ (x y : X), issymm (ER x y))
           (x y : poly_act P X)
  : issymm (poly_act_hrel P ER x y).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ _ _ p, ! p).
  - exact (HER x y).
  - intros r.
    induction x as [x | x], y as [y | y].
    + exact (IHP₁ _ _ r).
    + exact (fromempty r).
    + exact (fromempty r).
    + exact (IHP₂ _ _ r).
  - intros ? ? r.
    exact (IHP₁ _ _ _ _ (pr1 r) ,, IHP₂ _ _ _ _ (pr2 r)).
Qed.

Definition poly_act_iseqrel
           (P : poly_code)
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), eqrel (R x y))
           (x y : poly_act P X)
  : iseqrel (poly_act_hrel P ER x y).
Proof.
  refine ((_ ,, _) ,, _).
  - refine (poly_act_hrel_istrans P ER _ x y).
    apply ER.
  - refine (poly_act_hrel_isrefl P ER _ x y).
    apply ER.
  - refine (poly_act_hrel_issymm P ER _ x y).
    apply ER.
Defined.

Definition poly_act_eqrel
           (P : poly_code)
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), eqrel (R x y))
           (x y : poly_act P X)
  : eqrel (poly_act_rel P R x y).
Proof.
  use make_eqrel.
  - exact (poly_act_hrel P ER x y).
  - exact (poly_act_iseqrel P ER x y).
Defined.
      
Definition poly_act_quot_rel
           {P : poly_code}
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), eqrel (R x y))
           {x y : poly_act P X}
  : poly_act_rel P (quot_rel R ER) x y
    →
    quot_rel
      (poly_act_rel P R)
      (poly_act_eqrel P ER)
      x
      y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (setquotpr _).
  - exact (λ z, z).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + exact fromempty.
    + exact fromempty.
    + exact (IHP₂ x y).
  - intros z.
    specialize (IHP₁ _ _ (pr1 z)).
    specialize (IHP₂ _ _ (pr2 z)).
    revert IHP₁.
    use setquotuniv'.
    + apply isasetsetquot.
    + intro r₁.
      revert IHP₂.
      use setquotuniv'.
      * apply isasetsetquot.
      * intros r₂.
        apply setquotpr.
        exact (r₁ ,, r₂).
      * abstract
          (intros r₂ r₂' f ;
           use iscompsetquotpr ; simpl ;
           refine (_ ,, _) ;
           [ apply poly_act_hrel_isrefl ;
             apply ER
           | exact f ]).
    + abstract
        (intros r₁ r₁' f ;
         revert IHP₂ ;
         use (setquotunivprop _ (λ _, make_hProp _ _)) ;
         [ exact (isasetsetquot _ _ _)
         | intros r₂ ;
           use iscompsetquotpr ; simpl ;
           refine (_ ,, _) ;
           [ exact f
           | apply poly_act_hrel_isrefl ;
             apply ER]]).
Defined.

Definition isaset_poly_act_rel_quot_rel
           {P : poly_code}
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), eqrel (R x y))
           {x y : poly_act P X}
  : isaset (poly_act_rel P (quot_rel R ER) x y).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (one_type_isofhlevel A _ _).
  - apply isasetsetquot.
  - induction x as [x | x], y as [y | y].
    + apply IHP₁.
    + apply isasetempty.
    + apply isasetempty.
    + apply IHP₂.
  - apply isasetdirprod.
    + apply IHP₁.
    + apply IHP₂.
Defined.

Definition quot_rel_poly_act
           {P : poly_code}
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), eqrel (R x y))
           {x y : poly_act P X}
  : quot_rel
      (poly_act_rel P R)
      (poly_act_eqrel P ER)
      x
      y
    →
    poly_act_rel P (quot_rel R ER) x y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - use setquotuniv'.
    + exact (one_type_isofhlevel A _ _).
    + exact (λ p, p).
    + exact (λ _ _ r, r).
  - exact (λ z, z).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + simpl.
      use setquotuniv'.
      * exact isasetempty.
      * exact (λ z, z).
      * exact (λ z, fromempty z).
    + simpl.
      use setquotuniv'.
      * exact isasetempty.
      * exact (λ z, z).
      * exact (λ z, fromempty z).
    + exact (IHP₂ x y).
  - use setquotuniv'.
    + apply isaset_poly_act_rel_quot_rel.
    + exact (λ r, IHP₁ _ _ (setquotpr _ (pr1 r)) ,, IHP₂ _ _ (setquotpr _ (pr2 r))).
    + abstract
        (intros r₁ r₂ f ;
         apply pathsdirprod ;
         [ apply maponpaths ;
           apply iscompsetquotpr ;
           exact (pr1 f)
         | apply maponpaths ;
           apply iscompsetquotpr ;
           exact (pr2 f)]).
Defined.

Definition poly_act_quot_rel_quot_rel_poly_act
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
           (ER : ∏ (x y : X), eqrel (R x y))
           (x y : poly_act P X)
           (z : quot_rel
                  (poly_act_rel P R)
                  (poly_act_eqrel P ER)
                  x
                  y)
  : poly_act_quot_rel ER (quot_rel_poly_act ER z) = z.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - revert z.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    + apply isasetsetquot.
    + exact (λ _, idpath _).
  - apply idpath.
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y z).
    + induction (setquotuniv
                   (λ _ _, make_hProp ∅ isapropempty)
                   (make_hSet ∅ isasetempty)
                   (λ z0, z0)
                   (λ z0, fromempty z0) z).
    + induction (setquotuniv
                   (λ _ _, make_hProp ∅ isapropempty)
                   (make_hSet ∅ isasetempty)
                   (λ z0, z0)
                   (λ z0, fromempty z0) z).
    + exact (IHP₂ x y z).
  - revert z.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    + apply isasetsetquot.
    + intros z ; simpl.
      specialize (IHP₁ (pr1 x) (pr1 y) (setquotpr _ (pr1 z))).
      specialize (IHP₂ (pr2 x) (pr2 y) (setquotpr _ (pr2 z))).
      etrans.
      {
        apply maponpaths.
        apply IHP₁.
      }
      etrans.
      {
        apply (@setquotuniv'_comm _ (poly_act_eqrel P₁ ER (pr1 x) (pr1 y))).
      }
      etrans.
      {
        apply maponpaths.
        apply IHP₂.
      }
      apply idpath.
Defined.

Definition quot_rel_poly_act_poly_act_quot_rel
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
           (ER : ∏ (x y : X), eqrel (R x y))
           (x y : poly_act P X)
           (z : poly_act_rel P (quot_rel R ER) x y)
  : quot_rel_poly_act ER (poly_act_quot_rel ER z) = z.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y z).
    + induction z.
    + induction z.
    + exact (IHP₂ x y z).
  - specialize (IHP₁ _ _ (pr1 z)).
    specialize (IHP₂ _ _ (pr2 z)).
    refine (_ @ pathsdirprod IHP₁ IHP₂) ; clear IHP₁ IHP₂.
    etrans.
    {
      apply maponpaths.
      simpl.
      apply idpath.
    }
    generalize (poly_act_quot_rel ER (pr1 z)).
    generalize (poly_act_quot_rel ER (pr2 z)).
    clear z.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    + use impred_isaprop ; intro.
      apply (@isaset_poly_act_rel_quot_rel (P₁ * P₂)).
    + intro z₂.
      use (setquotunivprop _ (λ _, make_hProp _ _)).
      * apply (@isaset_poly_act_rel_quot_rel (P₁ * P₂)).
      * intro z₁.
        apply idpath.
Defined.

Definition quot_rel_poly_act_identity
           {P : poly_code}
           {X : UU}
           {R : X → X → UU}
           (r : ∏ (x : X), R x x)
           (ER : ∏ (x y : X), eqrel (R x y))
           {x : poly_act P X}
  : quot_rel_poly_act
      ER
      (setquotpr
         _
         (poly_act_rel_identity
            P
            _
            r
            x))
    =
    poly_act_rel_identity
      P
      _
      (λ z, setquotpr _ (r z))
      x.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - exact (setquotpr_eq
             (poly_act_iseqrel I ER x x)
             _
             (r x)).
  - induction x as [x | x].
    + simpl.
      refine (_ @ IHP₁ x).
      apply maponpaths.
      exact (setquotpr_eq
               (poly_act_iseqrel (P₁ + P₂) ER (inl x) (inl x))
               _
               _).
    + simpl.
      refine (_ @ IHP₂ x).
      apply maponpaths.
      exact (setquotpr_eq
               (poly_act_iseqrel (P₁ + P₂) ER (inr x) (inr x))
               _
               _).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Qed.
