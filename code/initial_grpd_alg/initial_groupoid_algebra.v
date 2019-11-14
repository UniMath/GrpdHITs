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

Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.
Require Import initial_grpd_alg.W_poly.
Require Import initial_grpd_alg.relation_2.

Opaque comp_psfunctor.

Local Open Scope cat.

(** Encode-decode to characterize `I = I` *)
Definition poly_eq_fam : poly_code → UU.
Proof.
  intro P.
  induction P.
  - exact empty.
  - exact unit.
  - exact empty.
  - exact empty.
Defined.

Definition r_poly_eq_fam
  : poly_eq_fam I
  := tt.

Definition poly_eq_fam_encode
           {P : poly_code}
  : I = P → poly_eq_fam P.
Proof.
  intro p.
  induction p.
  exact r_poly_eq_fam.
Defined.

Definition poly_eq_fam_decode
           {P : poly_code}
  : poly_eq_fam P → I = P.
Proof.
  induction P.
  - exact fromempty.
  - exact (λ _, idpath _).
  - exact fromempty.
  - exact fromempty.
Defined.

Definition poly_eq_fam_encode_decode
           {P : poly_code}
           (p : I = P)
  : poly_eq_fam_decode (poly_eq_fam_encode p) = p.
Proof.
  induction p.
  apply idpath.
Defined.

Definition poly_eq_fam_decode_encode
           {P : poly_code}
           (k : poly_eq_fam P)
  : poly_eq_fam_encode (poly_eq_fam_decode k) = k.
Proof.
  induction P.
  - induction k.
  - apply isapropunit.
  - induction k.
  - induction k.
Defined.

Definition path_I_is_refl
           (p : I = I)
  : p = idpath I
  := !(poly_eq_fam_encode_decode p).

Definition no_path_I_prod
           {P₁ P₂ : poly_code}
           (p : I = P₁ * P₂)
  : ∅
  := poly_eq_fam_encode p.

Definition no_path_I_sum
           {P₁ P₂ : poly_code}
           (p : I = P₁ + P₂)
  : ∅
  := poly_eq_fam_encode p.





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
  induction p as [P x | P x y p IHp | P x y z p₁ IHp₁ p₂ IHp₂
                  | j x | P Q x y p IHp | P Q x y p IHp
                  | P Q x₁ x₂ y₁ y₂ p₁ IHp₁ p₂ IHp₂
                  | x y p IHp ].
  - exact (poly_act_rel_identity _ _ initial_alg_id _).
  - apply poly_act_rel_inv.
    + apply @initial_alg_inv.
    + exact IHp.
  - use (poly_act_rel_comp _ _ _ IHp₁ IHp₂).
    apply @initial_alg_comp.
  - apply initial_alg_path.
  - exact IHp.
  - exact IHp.
  - exact (IHp₁ ,, IHp₂).
  - apply initial_alg_ap.
    exact p.
Defined.

Definition initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_I_type
           {A P : poly_code}
           {J : UU}
           {JS : J → poly_code}
           {l r : ∏ j : J, endpoint A (JS j) I}
           {x y : poly_act P (initial_groupoid_algebra_ob_poly A)}
           (p : initial_groupoid_algebra_mor_el_poly l r P x y)
           (pP : I = P)
  : UU.
Proof.
  refine (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel p = _).
  induction pP.
  simpl.
  exact p.
Defined.

Definition initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_I
           {A P : poly_code}
           {J : UU}
           {JS : J → poly_code}
           {l r : ∏ j : J, endpoint A (JS j) I}
           {x y : poly_act P (initial_groupoid_algebra_ob_poly A)}
           (p : initial_groupoid_algebra_mor_el_poly l r P x y)
           (pP : I = P)
  : initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_I_type p pP.
Proof.
  induction p as [P x | P x y p IHp | P x y z p₁ IHp₁ p₂ IHp₂
                  | j x | P Q x y p IHp | P Q x y p IHp
                  | P Q x₁ x₂ y₁ y₂ p₁ IHp₁ p₂ IHp₂
                  | x y p IHp ].
  - induction pP ; apply idpath.
  - induction pP.
    unfold initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_I_type
    ; simpl.
    apply maponpaths.
    exact (IHp (idpath _)).
  - induction pP.
    unfold initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_I_type
    ; simpl.
    etrans.
    {
      apply maponpaths.
      exact (IHp₂ (idpath _)).
    }
    simpl.
    apply maponpaths_2.
    exact (IHp₁ (idpath _)).
  - unfold initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_I_type
    ; simpl.
    assert (pP = idpath _) as X.
    {
      apply path_I_is_refl.
    }
    rewrite X.
    apply idpath.
  - induction (no_path_I_sum pP).
  - induction (no_path_I_sum pP).
  - induction (no_path_I_prod pP).
  - assert (pP = idpath _) as X.
    {
      apply path_I_is_refl.
    }
    unfold initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_I_type
    ; simpl.
    rewrite X.
    apply idpath.
Qed.
    
Definition initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec
           {A : poly_code}
           {J : UU}
           {JS : J → poly_code}
           {l r : ∏ (j : J), endpoint A (JS j) I}
           {P : poly_code}
           {x y : poly_act P (initial_groupoid_algebra_ob_poly A)}
           (p : poly_act_rel P (initial_groupoid_algebra_mor_el_poly l r I) x y)
  : initial_groupoid_algebra_mor_el_poly_to_poly_act_rel
      (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly p)
    =
    p.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - induction p.
    apply idpath.
  - exact (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec_I
             p (idpath _)).
  - induction x as [x | x], y as [y | y].
    + apply IHP₁.
    + exact (fromempty p).
    + exact (fromempty p).
    + apply IHP₂.
  - exact (pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _)).
Qed.

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

Definition sem_endpoint_initial_terms
           {Σ : hit_signature}
           {P Q : poly_code}
           (e : endpoint (point_constr Σ) P Q)
           {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
           (f : poly_act_rel P initial_groupoid_algebra_mor_el x y)
  : poly_act_rel
      Q initial_groupoid_algebra_mor_el
      (sem_endpoint_UU
         e
         (poly_initial_alg (point_constr Σ))
         x)
      (sem_endpoint_UU
         e
         (poly_initial_alg (point_constr Σ))
         y).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ g | ].
  - (* Identity *)
    exact f.
  - (* Composition *)
    exact (IHe₂ _ _ (IHe₁ _ _ f)).
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
    exact (idpath _).
  - (* Constant map *)
    exact (maponpaths g f).
  - (* Constructor *)
    exact (initial_alg_ap (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly f)).
Defined.

Definition sem_homot_endpoint_initial
           {Σ : hit_signature}
           {Q : poly_code}
           {TR : poly_code}
           {al ar : endpoint (point_constr Σ) Q TR}
           {T : poly_code}
           {sl sr : endpoint (point_constr Σ) Q T}
           (p : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
           (z : poly_act Q (initial_groupoid_algebra_ob Σ))
           (p_arg :
              poly_act_rel
                TR
                initial_groupoid_algebra_mor_el
                (sem_endpoint_UU
                   al
                   (poly_initial_alg (point_constr Σ))
                   z)
                (sem_endpoint_UU
                   ar
                   (poly_initial_alg (point_constr Σ))
                   z))
  : poly_act_rel
      T
      initial_groupoid_algebra_mor_el
      (sem_endpoint_UU
         sl
         (poly_initial_alg (point_constr Σ))
         z)
      (sem_endpoint_UU
         sr
         (poly_initial_alg (point_constr Σ))
         z).
Proof.
  induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel.
    apply initial_alg_id.
  - apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel.
    apply initial_alg_inv.
    apply poly_act_rel_to_initial_groupoid_algebra_mor_el_poly.
    exact IHp.
  - apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel.
    refine (initial_alg_comp _ _).
    + apply poly_act_rel_to_initial_groupoid_algebra_mor_el_poly.
      exact IHP₁.
    + apply poly_act_rel_to_initial_groupoid_algebra_mor_el_poly.
      exact IHP₂.
  - apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel.
    apply initial_alg_id.
  - apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel.
    apply initial_alg_id.
  - apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel.
    apply initial_alg_id.
  - exact (pr1 IHp).
  - exact (pr2 IHp).
  - exact (IHp₁ ,, IHp₂).
  - exact IHp.
  - exact IHp.
  - apply initial_alg_path.
  - simpl.
    apply initial_alg_ap.
    apply poly_act_rel_to_initial_groupoid_algebra_mor_el_poly.
    apply IHp.
  - exact p_arg.
Defined.

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
  | initial_alg_ap_id
    : ∏ (x : poly_act (point_constr Σ) (initial_groupoid_algebra_ob Σ)),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_ap
           (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
              (poly_act_rel_identity
                 (point_constr Σ)
                 (initial_groupoid_algebra_mor_el_poly (path_left Σ) (path_right Σ) I)
                 initial_alg_id x)))
        (initial_alg_id _)
  | initial_alg_ap_comp
    : ∏ (x y z : poly_act (point_constr Σ) (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly (point_constr Σ) x y)
        (g : initial_groupoid_algebra_mor_poly (point_constr Σ) y z),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_ap
           (initial_alg_comp f g))
        (initial_alg_comp
           (initial_alg_ap f)
           (initial_alg_ap g))
  | initial_alg_inl_path2
    : ∏ (P Q : poly_code)
        (x y : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P x y)
        (g : initial_groupoid_algebra_mor_poly P x y),
      initial_groupoid_algebra_mor_el_eq_UU f g
      →
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_inl_path P Q f)
        (initial_alg_inl_path P Q g)
  | initial_alg_inl_path_comp
    : ∏ (P Q : poly_code)
        (x y z : poly_act P (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly P x y)
        (g : initial_groupoid_algebra_mor_poly P y z),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_inl_path
           P Q
           (initial_alg_comp f g))
        (initial_alg_comp
           (initial_alg_inl_path P Q f)
           (initial_alg_inl_path P Q g))
  | initial_alg_inr_path2
    : ∏ (P Q : poly_code)
        (x y : poly_act Q (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly Q x y)
        (g : initial_groupoid_algebra_mor_poly Q x y),
      initial_groupoid_algebra_mor_el_eq_UU f g
      →
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_inr_path P Q f)
        (initial_alg_inr_path P Q g)
  | initial_alg_inr_path_comp
    : ∏ (P Q : poly_code)
        (x y z : poly_act Q (initial_groupoid_algebra_ob Σ))
        (f : initial_groupoid_algebra_mor_poly Q x y)
        (g : initial_groupoid_algebra_mor_poly Q y z),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_inr_path
           P Q
           (initial_alg_comp f g))
        (initial_alg_comp
           (initial_alg_inr_path P Q f)
           (initial_alg_inr_path P Q g))
  | initial_alg_pair_path2
    : ∏ (P Q : poly_code)
        (x₁ y₁ : poly_act P (initial_groupoid_algebra_ob Σ))
        (x₂ y₂ : poly_act Q (initial_groupoid_algebra_ob Σ))
        (f₁ f₂ : initial_groupoid_algebra_mor_poly P x₁ y₁)
        (g₁ g₂ : initial_groupoid_algebra_mor_poly Q x₂ y₂),
      initial_groupoid_algebra_mor_el_eq_UU f₁ f₂
      →
      initial_groupoid_algebra_mor_el_eq_UU g₁ g₂
      →
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_pair_path f₁ g₁)
        (initial_alg_pair_path f₂ g₂)
  | initial_alg_pair_path_comp
    : ∏ (P Q : poly_code)
        (x₁ y₁ z₁ : poly_act P (initial_groupoid_algebra_ob Σ))
        (x₂ y₂ z₂ : poly_act Q (initial_groupoid_algebra_ob Σ))
        (f₁ : initial_groupoid_algebra_mor_poly P x₁ y₁)
        (g₁ : initial_groupoid_algebra_mor_poly P y₁ z₁)
        (f₂ : initial_groupoid_algebra_mor_poly Q x₂ y₂)
        (g₂ : initial_groupoid_algebra_mor_poly Q y₂ z₂),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_pair_path
           (initial_alg_comp f₁ g₁)
           (initial_alg_comp f₂ g₂))
        (initial_alg_comp
           (initial_alg_pair_path f₁ f₂)
           (initial_alg_pair_path g₁ g₂))
  | initial_alg_ap2
    : ∏ (x y : poly_act (point_constr Σ) (initial_groupoid_algebra_ob Σ))
        (f g : initial_groupoid_algebra_mor_poly (point_constr Σ) x y),
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
        (initial_alg_id y)
  | path_constr_is_natural
    : ∏ (j : path_label Σ)
        (x y : poly_act (path_source Σ j) (initial_groupoid_algebra_ob Σ))
        (p : poly_act_rel
               (path_source Σ j)
               initial_groupoid_algebra_mor_el x y),
      initial_groupoid_algebra_mor_el_eq_UU
        (initial_alg_comp
           (initial_alg_path (path_left Σ) (path_right Σ) j x)
           (sem_endpoint_initial_terms (path_right Σ j) p))
        (initial_alg_comp
           (sem_endpoint_initial_terms (path_left Σ j) p)
           (initial_alg_path (path_left Σ) (path_right Σ) j y))
  | initial_alg_homotopy
    : ∏ (j : homot_label Σ)
        (z : poly_act
               (homot_point_arg Σ j)
               (initial_groupoid_algebra_ob Σ))
        (p : poly_act_rel
               (homot_path_arg_target Σ j)
               initial_groupoid_algebra_mor_el
               (sem_endpoint_UU
                  (homot_path_arg_left Σ j)
                  (poly_initial_alg (point_constr Σ))
                  z)
               (sem_endpoint_UU
                  (homot_path_arg_right Σ j)
                  (poly_initial_alg (point_constr Σ))
                  z)),
      initial_groupoid_algebra_mor_el_eq_UU
        (sem_homot_endpoint_initial (homot_left_path Σ j) z p)
        (sem_homot_endpoint_initial (homot_right_path Σ j) z p).

Arguments initial_alg_refl {_ _ _ _} _.
Arguments initial_alg_sym {_ _ _ _ _ _} _.
Arguments initial_alg_trans {_ _ _ _ _ _ _} _ _.
Arguments initial_alg_ap_id {_} _.
Arguments initial_alg_ap_comp {_ _ _ _} _ _.
Arguments initial_alg_inl_path2 {_} _ _ {_ _ _ _} _.
Arguments initial_alg_inl_path_comp {_} _ _ {_ _ _} _ _.
Arguments initial_alg_inr_path2 {_} _ _ {_ _ _ _} _.
Arguments initial_alg_inr_path_comp {_} _ _ {_ _ _} _ _.
Arguments initial_alg_pair_path2 {_ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments initial_alg_pair_path_comp {_ _ _ _ _ _ _ _ _} _ _ _ _.
Arguments initial_alg_pair_path_comp {_} _ _ {_ _ _} _ _.
Arguments initial_alg_ap2 {_ _ _ _ _} _.
Arguments initial_alg_inv_eq {_ _ _ _ _ _} _.
Arguments initial_alg_eq_lwhisker {_ _ _ _ _ _ _} _ _.
Arguments initial_alg_eq_rwhisker {_ _ _ _ _} _ {_ _} _.
Arguments initial_alg_left_unit {_ _ _ _} _.
Arguments initial_alg_right_unit {_ _ _ _} _.
Arguments initial_alg_assoc {_ _ _ _ _ _} _ _ _.
Arguments initial_alg_left_inv {_ _ _ _} _.
Arguments initial_alg_right_inv {_ _ _ _} _.
Arguments path_constr_is_natural {_} _ {_ _} _.
Arguments initial_alg_homotopy {_} _ _ _.

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
  
  Definition poly_act_rel2_to_initial_groupoid_algebra_mor_el_eq_UU
           {P : poly_code}
           {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
           (f g : poly_act_rel P (initial_groupoid_algebra_mor_el_poly _ _ I) x y)
    : poly_act_rel2
        P
        (λ (x y : initial_groupoid_algebra_ob Σ)
           (f g : initial_groupoid_algebra_mor_el x y),
         ishinh_UU (initial_groupoid_algebra_mor_el_eq_UU f g))
        f
        g
      →
      ishinh_UU
        (initial_groupoid_algebra_mor_el_eq_UU
           (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly f)
           (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly g)).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - intro p.
      induction p.
      apply hinhpr.
      apply initial_alg_refl.
    - exact (λ z, z).
    - induction x as [x | x], y as [y | y].
      + intro r.
        pose (IHP₁ x y f g r) as i.
        refine (factor_through_squash _ _ i).
        { apply ishinh. }
        intro z ; clear i r IHP₁ IHP₂.
        simpl in f, g.
        apply hinhpr.
        apply initial_alg_inl_path2.
        exact z.
      + induction f.
      + induction f.
      + intro r.
        pose (IHP₂ x y f g r) as i.
        refine (factor_through_squash _ _ i).
        { apply ishinh. }
        intro z ; clear i r IHP₁ IHP₂.
        simpl in f, g.
        apply hinhpr.
        apply initial_alg_inr_path2.
        exact z.
    - intro r.
      specialize (IHP₁ _ _ (pr1 f) (pr1 g) (pr1 r)).
      specialize (IHP₂ _ _ (pr2 f) (pr2 g) (pr2 r)).
      refine (factor_through_squash _ _ IHP₁).
      { apply ishinh. }
      intro i₁ ; clear IHP₁.
      refine (factor_through_squash _ _ IHP₂).
      { apply ishinh. }
      intro i₂ ; clear IHP₂.
      apply hinhpr.
      exact (initial_alg_pair_path2 i₁ i₂).
  Qed.

  Definition initial_groupoid_algebra_point_constr_data_morph
             {x y : poly_act_groupoid (point_constr Σ) initial_groupoid_algebra_carrier}
             (f : quot_rel
                    (poly_act_rel (point_constr Σ) initial_groupoid_algebra_mor_el)
                    (λ x y,
                     poly_act_eqrel
                       (point_constr Σ)
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
      pose (poly_act_rel2_to_initial_groupoid_algebra_mor_el_eq_UU _ _ r)
        as i.
      refine (factor_through_squash _ _ i).
      { apply ishinh. }
      intro z ; clear i.
      apply hinhpr.
      apply initial_alg_ap2.
      exact z.
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

  Definition initial_groupoid_algebra_point_constr_is_functor_id
             (P : poly_code)
             (z : poly_act_groupoid P initial_groupoid_algebra_carrier)
    : poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel (poly_act_identity z)
      =
      setquotpr
        (poly_act_eqrel
           P
           initial_groupoid_algebra_mor_el_eqrel
           z z)
        (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel
           (initial_alg_id _)).
  Proof.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - apply idpath.
    - simpl.
      apply setquotpr_eq.
    - induction z as [z | z].
      + refine (IHP₁ z @ _).
        apply setquotpr_eq.
      + refine (IHP₂ z @ _).
        apply setquotpr_eq.
    - simpl.
      etrans.
      {
        apply maponpaths.
        apply IHP₁.
      }
      simpl.
      etrans.
      {
        apply (@setquotuniv'_comm
                 _
                 (poly_act_eqrel
                    P₁
                    initial_groupoid_algebra_mor_el_eqrel
                    (pr1 z) (pr1 z))).
      }
      etrans.
      {
        apply maponpaths.
        apply IHP₂.
      }
      apply idpath.
  Qed.

  Definition initial_groupoid_algebra_point_constr_is_functor_help_comp
             (P : poly_code)
             {x y z : poly_act_groupoid P initial_groupoid_algebra_carrier}
             (f : setquot
                    (poly_act_hrel
                       P
                       (λ x y, @initial_groupoid_algebra_mor_el_eq x y)
                       x y))
             (g : setquot
                    (poly_act_hrel
                       P
                       (λ x y, @initial_groupoid_algebra_mor_el_eq x y)
                       y z))
    : setquot
        (poly_act_eqrel
           P
           (λ x0 y0, @initial_groupoid_algebra_mor_el_eqrel x0 y0) x z).
  Proof.
    revert f.
    use setquotuniv'.
    - apply isasetsetquot.
    - intro f.
      revert g.
      use setquotuniv'.
      + apply isasetsetquot.
      + intro g.
        apply setquotpr.
        refine (poly_act_rel_comp _ _ _ f g).
        clear x y z f g.
        intros x y z f g.
        exact (initial_alg_comp f g).
      + abstract
          (intros g₁ g₂ r ;
           apply iscompsetquotpr ;
           induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ;
           [ induction r ;
             apply idpath
           | revert r ;
             use factor_through_squash ;
             [ apply ishinh
             | intro r ;
               apply hinhpr ;
               apply initial_alg_eq_rwhisker ;
               apply r ]
             | induction x as [x | x], y as [y | y] ;
               [ induction z as [z | z] ;
                 [ exact (IHP₁ x y z f g₁ g₂ r)
                 | induction g₁ ]
               | induction f
               | induction f
               | induction z as [z | z] ;
                 [ induction g₁
                 | exact (IHP₂ x y z f g₁ g₂ r)]]
               | exact (IHP₁ _ _ _ _ _ _ (pr1 r) ,, IHP₂ _ _ _ _ _ _ (pr2 r))]).
    - abstract
        (intros f₁ f₂ r ;
         revert g ;
         use (setquotunivprop
                (poly_act_eqrel
                   P
                   (λ x y, @initial_groupoid_algebra_mor_el_eqrel x y)
                   y z)
                (λ _, make_hProp _ _)) ;
         [ apply isasetsetquot
         | intro g ;
           apply iscompsetquotpr ; simpl ;
           induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ;
           [ induction r ;
             apply idpath
           | revert r ;
             use factor_through_squash ;
             [ apply ishinh
             | intro r ;
             apply hinhpr ;
             apply initial_alg_eq_lwhisker ;
             apply r]
           | induction x as [x | x], y as [y | y] ;
             [ induction z as [z | z] ;
               [ exact (IHP₁ x y z f₁ f₂ r g)
               | induction g ]
             | induction f₁
             | induction f₁
             | induction z as [z | z] ;
               [ induction g
               | exact (IHP₂ x y z f₁ f₂ r g)]]
           | exact (IHP₁ _ _ _ _ _ (pr1 r) _ ,, IHP₂ _ _ _ _ _ (pr2 r) _)]]).
  Defined.

  Definition initial_groupoid_algebra_point_constr_is_functor_help_comp_lem
             (P : poly_code)
             {x y z : poly_act_groupoid P initial_groupoid_algebra_carrier}
             (f : poly_act_morphism P initial_groupoid_algebra_carrier x y)
             (g : poly_act_morphism P initial_groupoid_algebra_carrier y z)
    : poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel (poly_act_compose f g)
      =
      initial_groupoid_algebra_point_constr_is_functor_help_comp
        P (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel f)
        (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel g).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - apply idpath.
    - revert g.
      use (setquotunivprop _ (λ _, make_hProp _ _)).
      { apply isasetsetquot. }
      intro g.
      revert f.
      use (setquotunivprop _ (λ _, make_hProp _ _)).
      intro f ; simpl.
      apply setquotpr_eq.
    - induction x as [x | x], y as [y | y].
      + induction z as [z | z].
        * refine (IHP₁ _ _ _ f g @ _).
          clear IHP₁ IHP₂.
          simpl in f, g ; simpl.
          generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel f).
          generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel g).
          clear f g.
          use (setquotunivprop _ (λ _, make_hProp _ _)).
          { use impred_isaprop ; intro ; apply isasetsetquot. }
          intro g.
          use (setquotunivprop _ (λ _, make_hProp _ _)).
          { apply isasetsetquot. }
          intro f.
          apply (@setquotpr_eq
                   _
                   (poly_act_eqrel
                      P₁
                      (λ x0 y0, initial_groupoid_algebra_mor_el_eqrel x0 y0)
                      x z)).
        * induction g.
      + induction f.
      + induction f.
      + induction z as [z | z].
        * induction g.
        * refine (IHP₂ _ _ _ f g @ _).
          clear IHP₁ IHP₂.
          simpl in f, g ; simpl.
          generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel f).
          generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel g).
          clear f g.
          use (setquotunivprop _ (λ _, make_hProp _ _)).
          { use impred_isaprop ; intro ; apply isasetsetquot. }
          intro g.
          use (setquotunivprop _ (λ _, make_hProp _ _)).
          { apply isasetsetquot. }
          intro f.
          apply (@setquotpr_eq
                   _
                   (poly_act_eqrel
                      P₂
                      (λ x0 y0, initial_groupoid_algebra_mor_el_eqrel x0 y0)
                      x z)).
    - specialize (IHP₁ _ _ _ (pr1 f) (pr1 g)).
      specialize (IHP₂ _ _ _ (pr2 f) (pr2 g)).
      simpl.
      rewrite IHP₁.
      rewrite IHP₂.
      generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel (pr1 f)).
      generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel (pr2 f)).
      generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel (pr1 g)).
      generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel (pr2 g)).
      clear IHP₁ IHP₂ f g.
      use (setquotunivprop _ (λ _, make_hProp _ _)).
      { repeat (use impred_isaprop ; intro) ; apply isasetsetquot. }
      intro g₂ ; simpl.
      use (setquotunivprop
             (poly_act_eqrel
                P₁
                (λ x0 y0, @initial_groupoid_algebra_mor_el_eqrel x0 y0)
                _ _)
             (λ _, make_hProp _ _)).
      { repeat (use impred_isaprop ; intro) ; apply isasetsetquot. }
      intro g₁ ; simpl.
      use (setquotunivprop
             (poly_act_eqrel
                P₂
                (λ x0 y0, @initial_groupoid_algebra_mor_el_eqrel x0 y0)
                _ _)
             (λ _, make_hProp _ _)).
      { use impred_isaprop ; intro ; apply isasetsetquot. }
      intro f₂ ; simpl.
      use (setquotunivprop
             (poly_act_eqrel
                P₁
                (λ x0 y0, @initial_groupoid_algebra_mor_el_eqrel x0 y0)
                _ _)
             (λ _, make_hProp _ _)).
      { apply isasetsetquot. }
      intro f₁ ; simpl.
      apply (@setquotpr_eq
               _
               (poly_act_eqrel (P₁ * P₂) initial_groupoid_algebra_mor_el_eqrel x z)).
  Qed.
  
  Definition initial_groupoid_algebra_point_constr_is_functor_help₂
             (P : poly_code)
             {x y z : poly_act_groupoid P initial_groupoid_algebra_carrier}
             (f : poly_act_rel P initial_groupoid_algebra_mor_el x y)
             (g : poly_act_rel P initial_groupoid_algebra_mor_el y z)
    : initial_groupoid_algebra_mor_el_eq_UU
        (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
           (poly_act_rel_comp
              P initial_groupoid_algebra_mor_el
              (λ _ _ _ f0 g0, initial_alg_comp f0 g0)
              f g))
        (initial_alg_comp
           (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly f)
           (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly g)).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - induction f, g.
      simpl.
      apply initial_alg_sym.
      apply initial_alg_left_unit.
    - simpl.
      apply initial_alg_refl.
    - induction x as [x | x], y as [y | y].
      + induction z as [z | z].
        * specialize (IHP₁ x y z f g) ; clear IHP₂.
          simpl ; simpl in IHP₁.
          refine (initial_alg_trans
                    (initial_alg_inl_path2 _ _ IHP₁)
                    _).
          apply initial_alg_inl_path_comp.
        * induction g.
      + induction f.
      + induction f.
      + induction z as [z | z].
        * induction g.
        * specialize (IHP₂ x y z f g) ; clear IHP₁.
          refine (initial_alg_trans
                    (initial_alg_inr_path2 _ _ IHP₂)
                    _).
          apply initial_alg_inr_path_comp.
    - specialize (IHP₁ _ _ _ (pr1 f) (pr1 g)).
      specialize (IHP₂ _ _ _ (pr2 f) (pr2 g)).
      refine (initial_alg_trans
                (initial_alg_pair_path2 IHP₁ IHP₂)
                _).
      apply initial_alg_pair_path_comp.
  Qed.
      
  Definition initial_groupoid_algebra_point_constr_is_functor
    : is_functor initial_groupoid_algebra_point_constr_data.
  Proof.
    split.
    - intro x.
      simpl.
      rewrite !initial_groupoid_algebra_point_constr_is_functor_id.
      cbn.
      use (@iscompsetquotpr
             _
             (@initial_groupoid_algebra_mor_el_eqrel
                (poly_initial_alg (point_constr Σ) _)
                (poly_initial_alg (point_constr Σ) _))).
      apply hinhpr.
      simpl in x.
      cbn.
      apply initial_alg_ap_id.
    - intros x y z f g.
      simpl.
      cbn.
      cbn in f, g.
      etrans.
      {
        apply maponpaths.
        apply initial_groupoid_algebra_point_constr_is_functor_help_comp_lem.
      }
      generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel f).
      generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel g).
      clear f g.
      use (setquotunivprop _ (λ _, make_hProp _ _)).
      { use impred ; intro ; apply isasetsetquot. }
      intro g.
      use (setquotunivprop _ (λ _, make_hProp _ _)).
      { apply isasetsetquot. }
      intro f.
      cbn.
      etrans.
      {
        apply (iscompsetquotpr
                 (initial_groupoid_algebra_mor_el_eqrel
                    (poly_initial_alg (point_constr Σ) x)
                    (poly_initial_alg (point_constr Σ) z))).
        apply hinhpr.
        apply @initial_alg_ap2.
        apply initial_groupoid_algebra_point_constr_is_functor_help₂.
      }
      apply (iscompsetquotpr
               (initial_groupoid_algebra_mor_el_eqrel
                  (poly_initial_alg (point_constr Σ) x)
                  (poly_initial_alg (point_constr Σ) z))).
      apply hinhpr.      
      apply initial_alg_ap_comp.
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

  Definition sem_endpoint_initial_welldef_help
             {P : poly_code}
             {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
             {z₁ z₂ : poly_act_rel P initial_groupoid_algebra_mor_el x y}
             (p : poly_act_rel2
                    P
                    (λ _ _ x0 x1,
                     ishinh_UU (initial_groupoid_algebra_mor_el_eq_UU x0 x1))
                    z₁ z₂)
    : ishinh_UU
        (initial_groupoid_algebra_mor_el_eq_UU
           (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly z₁)
           (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly z₂)).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - apply hinhpr.
      induction p.
      apply initial_alg_refl.
    - exact p.
    - induction x as [x | x], y as [y | y].
      + specialize (IHP₁ x y z₁ z₂ p).
        use (factor_through_squash _ _ IHP₁).
        { apply ishinh. }
        intro h.
        apply hinhpr ; simpl.
        apply initial_alg_inl_path2.
        exact h.
      + induction z₁.
      + induction z₁.
      + specialize (IHP₂ x y z₁ z₂ p).
        use (factor_through_squash _ _ IHP₂).
        { apply ishinh. }
        intro h.
        apply hinhpr ; simpl.
        apply initial_alg_inr_path2.
        exact h.
    - specialize (IHP₁ (pr1 x) (pr1 y) (pr1 z₁) (pr1 z₂) (pr1 p)).
      specialize (IHP₂ (pr2 x) (pr2 y) (pr2 z₁) (pr2 z₂) (pr2 p)).
      use (factor_through_squash _ _ IHP₁).
      { apply ishinh. }
      intro h₁.
      use (factor_through_squash _ _ IHP₂).
      { apply ishinh. }
      intro h₂.
      apply hinhpr ; simpl.
      apply initial_alg_pair_path2.
      + exact h₁.
      + exact h₂.
  Qed.
      
  Definition sem_endpoint_initial_welldef
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
             {z₁ z₂ : poly_act_rel P initial_groupoid_algebra_mor_el x y}
             (p : poly_act_eqrel P initial_groupoid_algebra_mor_el_eqrel x y z₁ z₂)
    : poly_act_eqrel
        Q initial_groupoid_algebra_mor_el_eqrel
        (sem_endpoint_UU e (poly_initial_alg (point_constr Σ)) x)
        (sem_endpoint_UU e (poly_initial_alg (point_constr Σ)) y)
        (sem_endpoint_initial_terms e z₁) 
        (sem_endpoint_initial_terms e z₂).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | C₁ C₂ g | ].
    - (* Identity *)
      exact p.
    - (* Composition *)
      exact (IHe₂ _ _ _ _ (IHe₁ _ _ _ _ p)).
    - (* Left inclusion *)
      exact p.
    - (* Right inclusion *)
      exact p.
    - (* Left projection *)
      exact (pr1 p).
    - (* Right projection *)
      exact (pr2 p).
    - (* Pairing *)
      exact (IHe₁ _ _ _ _ p ,, IHe₂ _ _ _ _ p).
    - (* Constant *)
      exact (idpath _).
    - (* Constant map *)
      exact (maponpaths (maponpaths g) p).
    - (* Constructor *)
      simpl.
      pose (sem_endpoint_initial_welldef_help p) as h.
      use (factor_through_squash _ _ h).
      { apply ishinh. }
      clear h ; intro h.
      apply hinhpr.
      apply initial_alg_ap2.
      exact h.
  Qed.
    
  Definition sem_endpoint_initial
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
    : setquot
        (poly_act_eqrel
           P
           initial_groupoid_algebra_mor_el_eqrel
           x y)
      →
      setquot
        (poly_act_eqrel
           Q
           initial_groupoid_algebra_mor_el_eqrel
           (sem_endpoint_UU
              e
              (poly_initial_alg (point_constr Σ))
              x)
           (sem_endpoint_UU
              e
              (poly_initial_alg (point_constr Σ))
              y)).
  Proof.
    use setquotuniv'.
    - apply isasetsetquot.
    - intro z.
      use setquotpr.
      exact (sem_endpoint_initial_terms e z).
    - intros z₁ z₂ p.
      apply iscompsetquotpr.
      exact (sem_endpoint_initial_welldef _ p).
  Defined.

  Definition initial_groupoid_algebra_path_constr_is_nat_trans_help
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
    : ∏ (f : setquot
               (poly_act_eqrel
                  P
                  initial_groupoid_algebra_mor_el_eqrel
                  x y)),
      sem_endpoint_grpd_data_functor_morphism
        e
        initial_groupoid_algebra_point_constr
        (quot_rel_poly_act _ f)
      =
      quot_rel_poly_act
        _
        (sem_endpoint_initial e f).
  Proof.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    { apply poly_act_isaset_mor. }
    intros f ; simpl.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | C₁ C₂ g | ].
    - (* Identity *)
      apply idpath.
    - (* Composition *)
      simpl.
      etrans.
      {
        apply maponpaths.
        apply IHe₁.
      }
      exact (IHe₂ _ _ _).
    - (* Left inclusion *)
      simpl.
      apply maponpaths.
      apply setquotpr_eq.
    - (* Right inclusion *)
      simpl.
      apply maponpaths.
      apply setquotpr_eq.      
    - (* Left projection *)
      apply idpath.
    - (* Right projection *)
      apply idpath.
    - (* Pairing *)
      exact (pathsdirprod (IHe₁ _ _ _) (IHe₂ _ _ _)).
    - (* Constant *)
      exact (idpath _).
    - (* Constant map *)
      apply idpath.
    - (* Constructor *)
      simpl.
      etrans.
      {
        apply maponpaths.
        apply poly_act_quot_rel_quot_rel_poly_act.
      }
      apply setquotpr_eq.      
  Qed.
                                                         
  Definition initial_groupoid_algebra_path_constr_is_nat_trans
             (j : path_label Σ)
    : is_nat_trans
        _ _
        (initial_groupoid_algebra_path_constr_data j).
  Proof.
    intros x y f ; simpl in *.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (!(quot_rel_poly_act_poly_act_quot_rel _ _ _ _ _ f)).
      }
      rewrite initial_groupoid_algebra_path_constr_is_nat_trans_help.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(quot_rel_poly_act_poly_act_quot_rel _ _ _ _ _ f)).
      }
      rewrite initial_groupoid_algebra_path_constr_is_nat_trans_help.
      apply idpath.
    }
    simpl.
    generalize (poly_act_quot_rel initial_groupoid_algebra_mor_el_eqrel f).
    clear f.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    - apply isasetsetquot.
    - intros p.
      simpl ; cbn.
      apply (iscompsetquotpr (initial_groupoid_algebra_mor_el_eqrel _ _)).
      apply hinhpr.
      apply path_constr_is_natural.
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

  Definition quot_rel_poly_act_inv
             {P : poly_code}
             {x y : poly_act P (initial_groupoid_algebra_ob Σ)}
             (f : poly_act_rel
                    P
                    (initial_groupoid_algebra_mor_el_poly
                       (path_left Σ)
                       (path_right Σ)
                       I)
                    x y)
    : quot_rel_poly_act
        initial_groupoid_algebra_mor_el_eqrel
        (setquotpr
           _
           (poly_act_rel_inv
              _
              _
              (@initial_alg_inv
                 (point_constr Σ) (path_label Σ) (path_source Σ) 
                 (path_left Σ) (path_right Σ) I)
              f))
      =
      poly_act_rel_inv
        P
        _
        (λ _ _ g,
         initial_groupoid_algebra_carrier_comp
           (initial_groupoid_algebra_carrier_inv g)
           (initial_groupoid_algebra_carrier_id _))
        (quot_rel_poly_act
           _
           (setquotpr
              _
              f)).
  Proof.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - apply idpath.
    - refine (!_).
      etrans.
      {
        apply (iscompsetquotpr
                 (initial_groupoid_algebra_mor_el_eqrel y x)
                 _).
        simpl.
        apply hinhpr.
        exact (initial_alg_left_unit (initial_alg_inv f)).
      }
      refine (!_).
      exact (setquotpr_eq
               (poly_act_iseqrel I initial_groupoid_algebra_mor_el_eqrel y x)
               _
               _).
    - induction x as [x | x], y as [y | y].
      + simpl ; clear IHP₂.
        specialize (IHP₁ x y f).
        refine (_ @ IHP₁ @ _).
        * apply maponpaths.
          exact (setquotpr_eq
                   (poly_act_iseqrel (P₁ + P₂) _ (inl y) (inl x))
                   _
                   _).
        * do 2 apply maponpaths.
          exact (setquotpr_eq
                   _
                   (poly_act_iseqrel (P₁ + P₂) _ (inl x) (inl y))                   
                   _).
      + induction f.
      + induction f.
      + simpl ; clear IHP₁.
        specialize (IHP₂ x y f).
        refine (_ @ IHP₂ @ _).
        * apply maponpaths.
          exact (setquotpr_eq
                   (poly_act_iseqrel (P₁ + P₂) _ (inr y) (inr x))
                   _
                   _).
        * do 2 apply maponpaths.
          exact (setquotpr_eq
                   _
                   (poly_act_iseqrel (P₁ + P₂) _ (inr x) (inr y))                   
                   _).
    - exact (pathsdirprod (IHP₁ _ _ (pr1 f)) (IHP₂ _ _ (pr2 f))).
  Qed.

  Definition quot_rel_poly_act_comp
             {P : poly_code}
             {x y z : poly_act P (initial_groupoid_algebra_ob Σ)}
             (f : poly_act_rel
                    P
                    (initial_groupoid_algebra_mor_el_poly
                       (path_left Σ)
                       (path_right Σ)
                       I)
                    x y)
             (g : poly_act_rel
                    P
                    (initial_groupoid_algebra_mor_el_poly
                       (path_left Σ)
                       (path_right Σ)
                       I)
                    y z)
    : quot_rel_poly_act
        initial_groupoid_algebra_mor_el_eqrel
        (setquotpr
           _
           (poly_act_rel_comp
              _
              _
              (@initial_alg_comp (point_constr Σ) (path_label Σ) (path_source Σ) 
                                 (path_left Σ) (path_right Σ) I)
              f
              g))
      =
      poly_act_rel_comp
        _
        _
        (λ _ _ _ g₁ g₂, initial_groupoid_algebra_carrier_comp g₁ g₂)
        (quot_rel_poly_act
           initial_groupoid_algebra_mor_el_eqrel
           (setquotpr
              _
              f))
        (quot_rel_poly_act
           initial_groupoid_algebra_mor_el_eqrel
           (setquotpr
              _
              g)).
  Proof.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - apply idpath.
    - exact (setquotpr_eq
               (poly_act_iseqrel I initial_groupoid_algebra_mor_el_eqrel x z)
               _
               _).
    - induction x as [x | x], y as [y | y].
      + induction z as [z | z] ; [ | induction g].
        simpl ; clear IHP₂.
        specialize (IHP₁ _ _ _ f g).
        refine (_ @ IHP₁ @ _).
        * apply maponpaths.
          exact (setquotpr_eq
                   (poly_act_iseqrel (P₁ + P₂) _ (inl x) (inl z))
                   _
                   _).
        * etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (setquotpr_eq
                     (poly_act_iseqrel P₁ _ x y)
                     (poly_act_iseqrel (P₁ + P₂) _ (inl x) (inl y))
                     _).
          }
          do 2 apply maponpaths.
          exact (setquotpr_eq
                   (poly_act_iseqrel P₁ _ y z)
                   (poly_act_iseqrel (P₁ + P₂) _ (inl y) (inl z))
                   _).
      + induction f.
      + induction f.
      + induction z as [z | z] ; [ induction g | ].
        simpl ; clear IHP₁.
        specialize (IHP₂ _ _ _ f g).
        refine (_ @ IHP₂ @ _).
        * apply maponpaths.
          exact (setquotpr_eq
                   (poly_act_iseqrel (P₁ + P₂) _ (inr x) (inr z))
                   _
                   _).
        * etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (setquotpr_eq
                     (poly_act_iseqrel P₂ _ x y)
                     (poly_act_iseqrel (P₁ + P₂) _ (inr x) (inr y))
                     _).
          }
          do 2 apply maponpaths.
          exact (setquotpr_eq
                   (poly_act_iseqrel P₂ _ y z)
                   (poly_act_iseqrel (P₁ + P₂) _ (inr y) (inr z))
                   _).
    - exact (pathsdirprod (IHP₁ _ _ _ (pr1 f) (pr1 g)) (IHP₂ _ _ _ (pr2 f) (pr2 g))).
  Qed.

  Definition initial_groupoid_algebra_homot_constr_help_lem
             {Q : poly_code}
             {TR : poly_code}
             {al ar : endpoint (point_constr Σ) Q TR}
             {T : poly_code}
             {sl sr : endpoint (point_constr Σ) Q T}
             (p : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
             (z : poly_act Q (initial_groupoid_algebra_ob Σ))
             (p_arg :
                poly_act_rel
                  TR
                  initial_groupoid_algebra_mor_el
                  (sem_endpoint_UU
                     al
                     (poly_initial_alg (point_constr Σ))
                     z)
                  (sem_endpoint_UU
                     ar
                     (poly_initial_alg (point_constr Σ))
                     z))
    : sem_homot_endpoint_grpd
        p
        initial_groupoid_algebra_prealgebra initial_groupoid_algebra_path_constr
        z
        (quot_rel_poly_act
           initial_groupoid_algebra_mor_el_eqrel
           (setquotpr
              (poly_act_eqrel
                 TR
                 initial_groupoid_algebra_mor_el_eqrel
                 (sem_endpoint_UU
                    al
                    (poly_initial_alg (point_constr Σ)) z)
                 (sem_endpoint_UU
                    ar
                    (poly_initial_alg (point_constr Σ)) z))
              p_arg))
      =
      quot_rel_poly_act
        _
        (setquotpr
           _
           (sem_homot_endpoint_initial p z p_arg)).
  Proof.
    induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                    | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                    | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                    | j e | el er | ].
    - refine (!_).
      apply quot_rel_poly_act_identity.
    - simpl.
      etrans.
      {
        apply maponpaths.
        exact IHp.
      }
      clear IHp.
      refine (!_).
      refine (quot_rel_poly_act_inv
                (initial_groupoid_algebra_mor_el_poly_to_poly_act_rel
                   (poly_act_rel_to_initial_groupoid_algebra_mor_el_poly
                      (sem_homot_endpoint_initial p z p_arg)))
              @ _).
      do 2 apply maponpaths.
      apply maponpaths.
      apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec.
    - simpl.
      etrans.
      {
        apply maponpaths.
        exact IHP₂.
      }
      etrans.
      {
        apply maponpaths_2.
        exact IHP₁.
      }
      clear IHP₁ IHP₂.
      refine (!_).
      refine (quot_rel_poly_act_comp _ _ @ _).
      etrans.
      {
        do 3 apply maponpaths.
        apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec.
      }
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply initial_groupoid_algebra_mor_el_poly_to_poly_act_rel_spec.
      }
      apply idpath.
    - refine (!_).
      apply quot_rel_poly_act_identity.
    - refine (!_).
      apply quot_rel_poly_act_identity.
    - refine (!_).
      apply quot_rel_poly_act_identity.
    - simpl.
      etrans.
      {
        apply maponpaths.
        exact IHp.
      }
      apply idpath.
    - simpl.
      etrans.
      {
        apply maponpaths.
        exact IHp.
      }
      apply idpath.
    - exact (pathsdirprod IHp₁ IHp₂).
    - refine (IHp @ _).
      apply maponpaths.
      apply setquotpr_eq.
    - refine (IHp @ _).
      apply maponpaths.
      apply setquotpr_eq.
    - apply setquotpr_eq.
    - simpl.
      etrans.
      {
        do 2 apply maponpaths.
        exact IHp.
      }
      clear IHp.
      etrans.
      {
        apply maponpaths.
        apply poly_act_quot_rel_quot_rel_poly_act.
      }
      apply setquotpr_eq.
    - apply idpath.
  Qed.

  Definition initial_groupoid_algebra_homot_constr_help
             {j : homot_label Σ}
             (z : poly_act (homot_point_arg Σ j) (initial_groupoid_algebra_ob Σ))
             (p : quot_rel
                    (poly_act_rel
                       (homot_path_arg_target Σ j)
                       initial_groupoid_algebra_mor_el)
                    (λ x y,
                     poly_act_eqrel
                       (homot_path_arg_target Σ j)
                       initial_groupoid_algebra_mor_el_eqrel x y)
                    (sem_endpoint_UU
                       (homot_path_arg_left Σ j)
                       (poly_initial_alg (point_constr Σ))
                       z)
                    (sem_endpoint_UU
                       (homot_path_arg_right Σ j)
                       (poly_initial_alg (point_constr Σ))
                       z))
    : sem_homot_endpoint_grpd
        (homot_left_path Σ j)
        initial_groupoid_algebra_prealgebra
        initial_groupoid_algebra_path_constr
        z
        (quot_rel_poly_act
           initial_groupoid_algebra_mor_el_eqrel
           p)
      =
      sem_homot_endpoint_grpd
        (homot_right_path Σ j)
        initial_groupoid_algebra_prealgebra
        initial_groupoid_algebra_path_constr
        z
        (quot_rel_poly_act
           initial_groupoid_algebra_mor_el_eqrel
           p).
  Proof.
    revert p.
    use (setquotunivprop _ (λ _, make_hProp _ _)).
    - apply isasetsetquot.
    - intro p ; simpl.
      refine (initial_groupoid_algebra_homot_constr_help_lem
                (homot_left_path Σ j)
                z
                p
              @ _).
      refine (_
              @ !(initial_groupoid_algebra_homot_constr_help_lem
                    (homot_right_path Σ j)
                    z
                    p)) ; simpl.
      apply (iscompsetquotpr (poly_act_eqrel I initial_groupoid_algebra_mor_el_eqrel _ _)).
      simpl.
      apply hinhpr.
      apply initial_alg_homotopy.
  Qed.

  Definition initial_groupoid_algebra_homot_constr
    : is_hit_algebra_grpd Σ (initial_groupoid_algebra_path_algebra).
  Proof.
    intros j z p.
    simpl in *.
    unfold poly_act_morphism in p.
    etrans.
    {
      apply maponpaths.
      exact (!(quot_rel_poly_act_poly_act_quot_rel _ _ _ _ _ _)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(quot_rel_poly_act_poly_act_quot_rel _ _ _ _ _ _)).
    }
    refine (!_).
    apply initial_groupoid_algebra_homot_constr_help.
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
