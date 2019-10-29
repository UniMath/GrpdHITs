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
Require Import signature.hit.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.
Require Import initial_grpd_alg.W_poly.

Local Open Scope cat.

Local Definition TODO {A : Type} : A.
Admitted.

(*
Definition koe
           {A P Q : poly_code}
           {J : UU}
           {JS : J → poly_code}
           (l r : ∏ (j : J), endpoint A (JS j) I)
           (e : endpoint A P Q)
           {x y : poly_act P (initial_groupoid_algebra_ob_poly A)}
           (f : poly_act_rel P (initial_groupoid_algebra_mor_el_poly l r I) x y)
  : poly_act_rel
      Q
      (initial_groupoid_algebra_mor_el_poly l r I)
      (sem_endpoint_UU e (λ z, poly_initial_alg _ z) x)
      (sem_endpoint_UU e (λ z, poly_initial_alg _ z) y).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ g | ].
  - (* Identity *)
    exact f.
  - (* Composition *)
    exact (IHe₂ _ _ (IHe₁ x y f)).
  - (* Left inclusion *)
    exact f.
  - (* Right inclusion *)
    exact f.
  - (* Left projection *)
    exact (pr1 f).
  - (* Right projection *)
    exact (pr2 f).
  - (* Pairing *)
    exact (IHe₁ _ _ f ,, IHe₂ _ _ f).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    exact (maponpaths g f).
  - (* Constructor *)
    simpl.
    apply TODO.
Defined.
 *)

Definition setquotuniv'
           {X : UU}
           {R : hrel X}
           {Y : UU}
           {Yset : isaset Y}
           (f : X → Y)
           (H : iscomprelfun R f)
  : setquot R → Y
  := setquotuniv R (make_hSet Y Yset) f H.



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

Definition poly_act_rel_eqrel
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
           (ER : ∏ (x y : X), eqrel (R x y))
           (x y : poly_act P X)
  : eqrel (poly_act_rel P R x y).
Proof.
  use make_eqrel.
  - exact (λ r₁ r₂,
           make_hProp
             (poly_act_rel2 P (λ x y, pr1 (ER x y)) r₁ r₂)
             (isaprop_poly_act_rel2 P ER r₁ r₂)).
  - repeat split.
    + intros r₁ r₂ r₃ h₁ h₂ ; cbn in *.
      apply TODO.
    + intro r ; cbn.
      apply TODO.
    + intros r₁ r₂ h ; cbn in *.
      apply TODO.
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
      (poly_act_rel_eqrel P R ER)
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
  - apply TODO.
Defined.

Definition quot_rel_poly_act
           {P : poly_code}
           {X : UU}
           {R : X → X → UU}
           (ER : ∏ (x y : X), eqrel (R x y))
           {x y : poly_act P X}
  : quot_rel
      (poly_act_rel P R)
      (poly_act_rel_eqrel P R ER)
      x
      y
    →
    poly_act_rel P (quot_rel R ER) x y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - unfold quot_rel.
    simpl.
    apply TODO.
  - simpl.
    cbn.
    apply TODO.
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y).
    + apply TODO.
    + apply TODO.
    + exact (IHP₂ x y).
  - apply TODO.
Defined.
(*
Definition poly_act_quot_rel_quot_rel_poly_act
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
           (ER : ∏ (x y : X), eqrel (R x y))
           (x y : poly_act P X)
           z
  : poly_act_quot_rel P R ER x y (quot_rel_poly_act P R ER x y z) = z.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply TODO.
  - apply TODO.
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y z).
    + apply TODO.
    + apply TODO.
    + exact (IHP₂ x y z).
  - apply TODO.
Defined.

Definition quot_rel_poly_act_poly_act_quot_rel
           (P : poly_code)
           {X : UU}
           (R : X → X → UU)
           (ER : ∏ (x y : X), eqrel (R x y))
           (x y : poly_act P X)
           z
  : quot_rel_poly_act P R ER x y (poly_act_quot_rel P R ER x y z) = z.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply TODO.
  - apply TODO.
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ x y z).
    + apply TODO.
    + apply TODO.
    + exact (IHP₂ x y z).
  - apply TODO.
Defined.
 *)



Definition initial_groupoid_algebra_ob_poly
           (A : poly_code)
  : UU
  := poly_initial A.

Definition initial_groupoid_algebra_ob
           (Σ : hit_signature)
  := initial_groupoid_algebra_ob_poly (point_constr Σ).

Inductive initial_groupoid_algebra_mor_el_poly
          {A : poly_code}
          {J : UU}
          {JS : J → poly_code}
          (l r : ∏ (j : J), endpoint A (JS j) I)
  : ∏ (P : poly_code),
    poly_act P (initial_groupoid_algebra_ob_poly A)
    → poly_act P (initial_groupoid_algebra_ob_poly A)
    → UU
  :=
  | initial_alg_id
    : ∏ {P : poly_code}
        (x : poly_act P (initial_groupoid_algebra_ob_poly A)),
      initial_groupoid_algebra_mor_el_poly l r P x x
  | initial_alg_inv
    : ∏ {P : poly_code}
        (x y : poly_act P (initial_groupoid_algebra_ob_poly A)),
      initial_groupoid_algebra_mor_el_poly l r P x y
      →
      initial_groupoid_algebra_mor_el_poly l r P y x
  | initial_alg_comp
    : ∏ {P : poly_code}
        (x y z : poly_act P (initial_groupoid_algebra_ob_poly A)),
      initial_groupoid_algebra_mor_el_poly l r P x y
      →
      initial_groupoid_algebra_mor_el_poly l r P y z
      →
      initial_groupoid_algebra_mor_el_poly l r P x z
  | initial_alg_path
    : ∏ (j : J)
        (x : poly_act
               (JS j)
               (initial_groupoid_algebra_ob_poly A)),
      initial_groupoid_algebra_mor_el_poly
        l r I
        (sem_endpoint_UU
           (l j)
           (poly_initial_alg A)
           x)
        (sem_endpoint_UU
           (r j)
           (poly_initial_alg A)
           x)
  | initial_alg_inl_path
    : ∏ (P Q : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob_poly A)),
      initial_groupoid_algebra_mor_el_poly l r P x y
      →
      initial_groupoid_algebra_mor_el_poly l r (P + Q) (inl x) (inl y)
  | initial_alg_inr_path
    : ∏ (P Q : poly_code)
        (x y : poly_act Q (initial_groupoid_algebra_ob_poly A)),
      initial_groupoid_algebra_mor_el_poly l r Q x y
      →
      initial_groupoid_algebra_mor_el_poly l r (P + Q) (inr x) (inr y)
  | initial_alg_pair_path
    : ∏ (P Q : poly_code)
        (x₁ y₁ : poly_act P (initial_groupoid_algebra_ob_poly A))
        (x₂ y₂ : poly_act Q (initial_groupoid_algebra_ob_poly A)),
      initial_groupoid_algebra_mor_el_poly l r P x₁ y₁
      →
      initial_groupoid_algebra_mor_el_poly l r Q x₂ y₂
      →
      initial_groupoid_algebra_mor_el_poly
        l r (P * Q)
        (x₁ ,, x₂)
        (y₁ ,, y₂)
  | initial_alg_ap
    : ∏ (x y : poly_act A (initial_groupoid_algebra_ob_poly A)),
      initial_groupoid_algebra_mor_el_poly l r A x y
      →
      initial_groupoid_algebra_mor_el_poly
        l r I
        (poly_initial_alg A x)
        (poly_initial_alg A y).

Arguments initial_alg_id {_ _ _ _ _ _} _.
Arguments initial_alg_inv {_ _ _ _ _ _ _ _} _.
Arguments initial_alg_comp { _ _ _ _ _ _ _ _ _} _ _.
Arguments initial_alg_path {_ _ _} _ _ _ _.
Arguments initial_alg_inl_path {_ _ _ _ _} _ _ {_ _} _.
Arguments initial_alg_inr_path {_ _ _ _ _} _ _ {_ _} _.
Arguments initial_alg_pair_path {_ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments initial_alg_ap {_ _ _ _ _ _ _} _.

Definition poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
           {A : poly_code}
           {J : UU}
           {JS : J → poly_code}
           {l r : ∏ (j : J), endpoint A (JS j) I}
           {P : poly_code}
           {x y : poly_act P (initial_groupoid_algebra_ob_poly A)}
           (p : poly_act_rel P (initial_groupoid_algebra_mor_el_poly l r I) x y)
  : initial_groupoid_algebra_mor_el_poly l r P x y.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - induction p.
    apply initial_alg_id.
  - exact p.
  - induction x as [x | x], y as [y | y].
    + exact (initial_alg_inl_path _ _ (IHP₁ x y p)).
    + exact (fromempty p).
    + exact (fromempty p).
    + exact (initial_alg_inr_path _ _ (IHP₂ x y p)).
  - exact (initial_alg_pair_path (IHP₁ _ _ (pr1 p)) (IHP₂ _ _ (pr2 p))).
Defined.

Definition initial_groupoid_algebra_mor_el_poly_to_poly_act_rel
           {A : poly_code}
           {J : UU}
           {JS : J → poly_code}
           {l r : ∏ (j : J), endpoint A (JS j) I}
           {P : poly_code}
           {x y : poly_act P (initial_groupoid_algebra_ob_poly A)}
           (p : initial_groupoid_algebra_mor_el_poly l r P x y)
  : poly_act_rel P (initial_groupoid_algebra_mor_el_poly l r I) x y.
Proof.
  induction p.
  - exact (poly_act_rel_identity _ _ initial_alg_id _).
  - apply poly_act_rel_inv.
    + apply @initial_alg_inv.
    + exact IHp.
  - use (poly_act_rel_comp _ _ _ IHp1 IHp2).
    apply @initial_alg_comp.
  - apply initial_alg_path.
  - exact IHp.
  - exact IHp.
  - exact (IHp1 ,, IHp2).
  - apply initial_alg_ap.
    exact p.
Defined.

Definition initial_groupoid_algebra_mor_poly
           {Σ : hit_signature}
           (P : poly_code)
  : poly_act P (initial_groupoid_algebra_ob Σ)
    → poly_act P (initial_groupoid_algebra_ob Σ)
    → UU
  := initial_groupoid_algebra_mor_el_poly (path_left Σ) (path_right Σ) P.

Definition initial_groupoid_algebra_mor_el
           {Σ : hit_signature}
  : initial_groupoid_algebra_ob Σ → initial_groupoid_algebra_ob Σ → UU
  := initial_groupoid_algebra_mor_el_poly (path_left Σ) (path_right Σ) I.

Inductive initial_groupoid_algebra_mor_el_eq_UU
          {Σ : hit_signature}
  : ∏ {P : poly_code}
      {x y : poly_act P (initial_groupoid_algebra_ob Σ)},
    initial_groupoid_algebra_mor_poly P x y
    →
    initial_groupoid_algebra_mor_poly P x y
    → UU
  :=
  | initial_alg_refl
    : ∏ (P : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU f f
  | initial_alg_sym
    : ∏ (P : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f g : initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU f g
      →
      initial_groupoid_algebra_mor_el_eq_UU g f
  | initial_alg_trans
    : ∏ (P : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f g h: initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU f g
      →
      initial_groupoid_algebra_mor_el_eq_UU g h
      →
      initial_groupoid_algebra_mor_el_eq_UU f h
  | initial_alg_ap2
    : ∏ (x y : poly_act (point_constr Σ) (initial_groupoid_algebra_ob Σ))
        (f g: initial_groupoid_algebra_mor_poly (point_constr Σ) x y),
      initial_groupoid_algebra_mor_el_eq_UU f g
      →
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_ap f)
        (initial_alg_ap g)
  | initial_alg_inv_eq
    : ∏ (P : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f g : initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU f g
      →
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_inv f)
        (initial_alg_inv g)
  | initial_alg_eq_lwhisker
    : ∏ (P : poly_code)
        (x y z : poly_act P (initial_groupoid_algebra_ob Σ))
        (f₁ f₂ : initial_groupoid_algebra_mor_poly P x y)
        (g : initial_groupoid_algebra_mor_poly P y z),
      initial_groupoid_algebra_mor_el_eq_UU f₁ f₂
      →
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_comp f₁ g)
        (initial_alg_comp f₂ g)
  | initial_alg_eq_rwhisker
    : ∏ (P : poly_code)
        (x y z : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P x y)
        (g₁ g₂ : initial_groupoid_algebra_mor_poly P y z),
      initial_groupoid_algebra_mor_el_eq_UU g₁ g₂
      →
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_comp f g₁)
        (initial_alg_comp f g₂)
  | initial_alg_left_unit
    : ∏ (P : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_comp
           f
           (initial_alg_id y))
        f
  | initial_alg_right_unit
    : ∏ (P : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_comp
           (initial_alg_id x)
           f)
        f
  | initial_alg_assoc
    : ∏ (P : poly_code)
        (w x y z : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P w x)
        (g : initial_groupoid_algebra_mor_poly P x y)
        (h : initial_groupoid_algebra_mor_poly P y z),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_comp f (initial_alg_comp g h))
        (initial_alg_comp (initial_alg_comp f g) h)
  | initial_alg_left_inv
    : ∏ (P : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_comp
           f
           (initial_alg_inv f))
        (initial_alg_id x)
  | initial_alg_right_inv
    : ∏ (P : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_comp
           (initial_alg_inv f)
           f)
        (initial_alg_id y).

Arguments initial_alg_refl {_ _ _ _} _.
Arguments initial_alg_sym {_ _ _ _ _ _} _.
Arguments initial_alg_trans {_ _ _ _ _ _ _} _ _.
Arguments initial_alg_inv_eq {_ _ _ _ _ _} _.
Arguments initial_alg_eq_lwhisker {_ _ _ _ _ _ _} _ _.
Arguments initial_alg_eq_rwhisker {_ _ _ _ _} _ {_ _} _.
Arguments initial_alg_left_unit {_ _ _ _} _.
Arguments initial_alg_right_unit {_ _ _ _} _.
Arguments initial_alg_assoc {_ _ _ _ _ _} _ _ _.
Arguments initial_alg_left_inv {_ _ _ _} _.
Arguments initial_alg_right_inv {_ _ _ _} _.

Definition poly_act_rel2_to_initial_groupoid_algebra_mor_el_eq_UU
           {Σ : hit_signature}
           {P : poly_code}
           {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
           (f g : initial_groupoid_algebra_mor_poly P x y)
  : poly_act_rel2
      P
      (@initial_groupoid_algebra_mor_el_eq_UU Σ I)
      (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel f)
      (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel g)
    →
    initial_groupoid_algebra_mor_el_eq_UU f g.
Proof.
  apply TODO.
Defined.

Section InitialGroupoidAlg.
  Variable (Σ : hit_signature).

  Definition initial_groupoid_algebra_mor_el_eq
             {x y : initial_groupoid_algebra_ob Σ}
             (f g : initial_groupoid_algebra_mor_el x y)
    : hProp
    := ∥ initial_groupoid_algebra_mor_el_eq_UU f g ∥.

  Definition initial_groupoid_algebra_mor_el_eqrel
             (x y : initial_groupoid_algebra_ob Σ)
    : eqrel (initial_groupoid_algebra_mor_el x y).
  Proof.
    use make_eqrel.
    - exact initial_groupoid_algebra_mor_el_eq.
    - repeat split.
      + (* transitivity *)
        abstract
          (intros f g h ;
           use factor_through_squash ;
           [ use impred ; intro ; apply ishinh | ] ;
           intro r₁ ;
           use factor_through_squash ;
           [ apply ishinh | ] ;
           exact (λ r₂, hinhpr (initial_alg_trans r₁ r₂))).
      + (* reflexivity *)
        abstract (exact (λ f, hinhpr (initial_alg_refl f))).
      + (* symmetry *)
        abstract
          (intros f g ;
           use factor_through_squash ;
           [ apply ishinh | ] ;
           exact (λ r, hinhpr (initial_alg_sym r))).
  Defined.
  
  Definition initial_groupoid_algebra_mor
             (x y : initial_groupoid_algebra_ob Σ)
    : hSet
    := quot_rel _ initial_groupoid_algebra_mor_el_eqrel x y.

  Definition initial_groupoid_algebra_carrier_id
             (x : initial_groupoid_algebra_ob Σ)
    : initial_groupoid_algebra_mor x x
    := setquotpr _ (@initial_alg_id _ _ _ _ _ I x).

  Definition initial_groupoid_algebra_carrier_inv
             {x y : initial_groupoid_algebra_ob Σ}
    : initial_groupoid_algebra_mor x y
      →
      initial_groupoid_algebra_mor y x.
  Proof.
    use setquotuniv.
    - (* the element *)
      exact (λ f, setquotpr _ (initial_alg_inv f)).
    - (* well definedness *)
      abstract
        (intros f g ;
         use factor_through_squash ;
         [ exact (isasetsetquot _ _ _) | ] ;
         intro r ;
         apply iscompsetquotpr ;
         apply hinhpr ;
         exact (initial_alg_inv_eq r)).
  Defined.

  Definition initial_groupoid_algebra_carrier_comp
             {x y z : initial_groupoid_algebra_ob Σ}
    : initial_groupoid_algebra_mor x y
      →
      initial_groupoid_algebra_mor y z
      →
      initial_groupoid_algebra_mor x z.
  Proof.
    simple refine (setquotuniv _ (make_hSet _ _) _ _).
    - abstract (use impred_isaset ; intro ; apply isasetsetquot).
    - intros f.
      use setquotuniv.
      + (* the element *)
        exact (λ g, setquotpr _ (initial_alg_comp f g)).
      + (* whiskering *)
        abstract
          (intros g₁ g₂ ;
           use factor_through_squash ;
           [ exact (isasetsetquot _ _ _) | ] ;
           intro p ;
           apply iscompsetquotpr ;
           apply hinhpr ;
           exact (initial_alg_eq_rwhisker f p)).
    - (* whiskering *)
      abstract
        (intros f₁ f₂ ;
         use factor_through_squash ;
         [ exact (funspace_isaset (isasetsetquot _) _ _) | ] ;
         intro p ;
         use funextsec ; unfold homotsec ;
         use (setquotunivprop _ (λ _, make_hProp _ _)) ;
         [ exact (isasetsetquot _ _ _) | ] ;
         intros g ;
         apply iscompsetquotpr ;
         apply hinhpr ;
         exact (initial_alg_eq_lwhisker g p)).
  Defined.

  Definition initial_groupoid_algebra_carrier_left_unit
             {x y : initial_groupoid_algebra_ob Σ}
    : ∏ (f : initial_groupoid_algebra_mor x y),
      initial_groupoid_algebra_carrier_comp
        f
        (initial_groupoid_algebra_carrier_id y)
      =
      f.
  Proof.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    { exact (isasetsetquot _ _ _). }
    intro f.
    apply iscompsetquotpr.
    apply hinhpr.
    exact (initial_alg_left_unit f).
  Qed.      

  Definition initial_groupoid_algebra_carrier_right_unit
             {x y : initial_groupoid_algebra_ob Σ}
    : ∏ (f : initial_groupoid_algebra_mor x y),
      initial_groupoid_algebra_carrier_comp
        (initial_groupoid_algebra_carrier_id x)
        f
      =
      f.
  Proof.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    { exact (isasetsetquot _ _ _). }
    intro f.
    apply iscompsetquotpr.
    apply hinhpr.
    exact (initial_alg_right_unit f).
  Qed.

  Definition initial_groupoid_algebra_carrier_assoc
             {w x y z : initial_groupoid_algebra_ob Σ}
    : ∏ (f : initial_groupoid_algebra_mor w x)
        (g : initial_groupoid_algebra_mor x y)
        (h : initial_groupoid_algebra_mor y z),
      initial_groupoid_algebra_carrier_comp
        f
        (initial_groupoid_algebra_carrier_comp g h)
      =
      initial_groupoid_algebra_carrier_comp
        (initial_groupoid_algebra_carrier_comp f g)
        h.
  Proof.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    { do 2 (use impred ; intro) ; exact (isasetsetquot _ _ _). }
    intros f.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    { use impred ; intro ; exact (isasetsetquot _ _ _). }
    intros g.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    { exact (isasetsetquot _ _ _). }
    intros h.
    apply iscompsetquotpr.
    apply hinhpr.
    exact (initial_alg_assoc f g h).
  Qed.

  Definition initial_groupoid_algebra_carrier_right_inv
             {x y : initial_groupoid_algebra_ob Σ}
    : ∏ (f : initial_groupoid_algebra_mor x y),
      initial_groupoid_algebra_carrier_comp
        f
        (initial_groupoid_algebra_carrier_inv f)
      =
      initial_groupoid_algebra_carrier_id x.
  Proof.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    { exact (isasetsetquot _ _ _). }
    intro f.
    apply iscompsetquotpr.
    apply hinhpr.
    exact (initial_alg_left_inv f).
  Qed.      

  Definition initial_groupoid_algebra_carrier_left_inv
             {x y : initial_groupoid_algebra_ob Σ}
    : ∏ (f : initial_groupoid_algebra_mor x y),
      initial_groupoid_algebra_carrier_comp
        (initial_groupoid_algebra_carrier_inv f)
        f
      =
      initial_groupoid_algebra_carrier_id y.
  Proof.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    { exact (isasetsetquot _ _ _). }
    intro f.
    apply iscompsetquotpr.
    apply hinhpr.
    exact (initial_alg_right_inv f).
  Qed.
  
  Definition initial_groupoid_algebra_carrier
    : groupoid.
  Proof.
    use make_grpd_bicat.
    - (* objects *)
      exact (initial_groupoid_algebra_ob Σ).
    - (* morphisms *)
      exact initial_groupoid_algebra_mor.
    - (* identity *)
      exact initial_groupoid_algebra_carrier_id.
    - (* inverse *)
      exact @initial_groupoid_algebra_carrier_inv.
    - (* composition *)
      exact @initial_groupoid_algebra_carrier_comp.
    - (* left unitality *)
      exact @initial_groupoid_algebra_carrier_left_unit.
    - (* right unitality *)
      exact @initial_groupoid_algebra_carrier_right_unit.
    - (* associativity *)
      exact @initial_groupoid_algebra_carrier_assoc.
    - (* right inverse law *)
      exact @initial_groupoid_algebra_carrier_right_inv.
    - (* left inverse law *)
      exact @initial_groupoid_algebra_carrier_left_inv.
    - (* morphisms for a set *)
      exact (λ _ _, isasetsetquot _).
  Defined.


  Definition initial_groupoid_algebra_point_constr_data_morph
             {x y : poly_act_groupoid (point_constr Σ) initial_groupoid_algebra_carrier}
             (f : quot_rel
                    (poly_act_rel (point_constr Σ) initial_groupoid_algebra_mor_el)
                    (λ x y,
                     poly_act_rel_eqrel
                       (point_constr Σ)
                       initial_groupoid_algebra_mor_el
                       initial_groupoid_algebra_mor_el_eqrel x y)
                    x y)
    : setquot
        (@initial_groupoid_algebra_mor_el_eq
           (poly_initial_alg (point_constr Σ) x)
           (poly_initial_alg (point_constr Σ) y)).
  Proof.
    revert f.
    use setquotuniv'.
    - apply isasetsetquot.
    - intros f.
      use (@setquotpr
             _
             (@initial_groupoid_algebra_mor_el_eqrel
                (poly_initial_alg (point_constr Σ) x)
                (poly_initial_alg (point_constr Σ) y))).
      apply initial_alg_ap.
      exact (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly f).
    - intros f₁ f₂ r.
      use (@iscompsetquotpr
             _
             (@initial_groupoid_algebra_mor_el_eqrel
                (poly_initial_alg (point_constr Σ) x)
                (poly_initial_alg (point_constr Σ) y))).
      apply hinhpr.
      apply initial_alg_ap2.
      apply poly_act_rel2_to_initial_groupoid_algebra_mor_el_eq_UU.
      simpl in r.
      apply TODO.
  Defined.
  
  Definition initial_groupoid_algebra_point_constr_data
    : functor_data
        (poly_act_groupoid (point_constr Σ) initial_groupoid_algebra_carrier)
        (initial_groupoid_algebra_carrier).
  Proof.
    use make_functor_data.
    - (* on points *)
      exact (λ x, poly_initial_alg (point_constr Σ) x).
    - (* on morphisms *)
      intros x y f ; simpl.
      exact (initial_groupoid_algebra_point_constr_data_morph
               (poly_act_quot_rel _ f)).
  Defined.

  Definition initial_groupoid_algebra_point_constr_is_functor
    : is_functor initial_groupoid_algebra_point_constr_data.
  Proof.
    split.
    - intro x.
      simpl.
      cbn.
      unfold initial_groupoid_algebra_carrier_id.
      assert (∏ (P : poly_code)
                (z : poly_act_groupoid P initial_groupoid_algebra_carrier),
              poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel (poly_act_identity z)
              =
              setquotpr
                (poly_act_rel_eqrel
                   P initial_groupoid_algebra_mor_el
                   initial_groupoid_algebra_mor_el_eqrel
                   z z)
                (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel
                   (initial_alg_id _)
                )
             )
        as X.
      {
        apply TODO.
      }
      rewrite !X.
      cbn.
      use (@iscompsetquotpr
             _
             (@initial_groupoid_algebra_mor_el_eqrel
                (poly_initial_alg (point_constr Σ) _)
                (poly_initial_alg (point_constr Σ) _))).
      apply hinhpr.
      cbn.
      apply TODO.
    - intros x y z f g.
      simpl.
      cbn.
      cbn in f, g.
      unfold poly_act_morphism in f, g.
      unfold initial_groupoid_algebra_point_constr_data_morph.
      apply TODO.
  Qed.
      
  Definition initial_groupoid_algebra_point_constr
    : poly_act_groupoid (point_constr Σ) initial_groupoid_algebra_carrier
      ⟶
      initial_groupoid_algebra_carrier.
  Proof.
    use make_functor.
    - exact initial_groupoid_algebra_point_constr_data.
    - exact initial_groupoid_algebra_point_constr_is_functor.
  Defined.

  Definition initial_groupoid_algebra_prealgebra
    : hit_prealgebra_grpd Σ.
  Proof.
    use make_hit_prealgebra_grpd.
    - exact initial_groupoid_algebra_carrier.
    - exact initial_groupoid_algebra_point_constr.
  Defined.

  Definition initial_groupoid_algebra_path_constr_data
             (j : path_label Σ)
    : nat_trans_data
        (sem_endpoint_grpd_data_functor
           (path_left Σ j)
           initial_groupoid_algebra_prealgebra)
        (sem_endpoint_grpd_data_functor
           (path_right Σ j)
           initial_groupoid_algebra_prealgebra)
    := λ x, setquotpr _ (initial_alg_path _ _ j x).
 
  Definition initial_groupoid_algebra_path_constr_is_nat_trans
             (j : path_label Σ)
    : is_nat_trans
        _ _
        (initial_groupoid_algebra_path_constr_data j).
  Proof.
    intros x y f ; simpl in *.
    unfold initial_groupoid_algebra_path_constr_data.
    cbn.
    apply TODO.
  Qed.

  Definition initial_groupoid_algebra_path_constr
             (j : path_label Σ)
    : sem_endpoint_grpd_data_functor
        (path_left Σ j)
        initial_groupoid_algebra_prealgebra
      ⟹
      sem_endpoint_grpd_data_functor
        (path_right Σ j)
        initial_groupoid_algebra_prealgebra.
  Proof.
    use make_nat_trans.
    - exact (initial_groupoid_algebra_path_constr_data j).
    - exact (initial_groupoid_algebra_path_constr_is_nat_trans j).
  Defined.

  Definition initial_groupoid_algebra_path_algebra
    : hit_path_algebra_grpd Σ.
  Proof.
    use make_hit_path_algebra_grpd.
    - exact initial_groupoid_algebra_prealgebra.
    - exact initial_groupoid_algebra_path_constr.
  Defined.

  Definition initial_groupoid_algebra_homot_constr
    : is_hit_algebra_grpd Σ (initial_groupoid_algebra_path_algebra).
  Proof.
    intros j z p.
    simpl in *.
    apply TODO.
  Qed.
End InitialGroupoidAlg.

Definition initial_groupoid_algebra
           (Σ : hit_signature)
  : hit_algebra_grpd Σ.
Proof.
  use make_algebra_grpd.
  - exact (initial_groupoid_algebra_path_algebra Σ).
  - exact (initial_groupoid_algebra_homot_constr Σ).
Defined.
