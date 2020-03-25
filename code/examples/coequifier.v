(** Here we define the signature for the integers modulo 2 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

(** MISSING HOMOTOPY ENDPOINTS *)
Definition whisker_π₁
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {P₁ P₂ : poly_code}
           {e₁ e₂ : endpoint A Q (P₁ * P₂)}
           (h : homot_endpoint
                  l r
                  al ar
                  e₁
                  e₂)
  : homot_endpoint
      l r
      al ar
      (comp e₁ (π₁ _ _))
      (comp e₂ (π₁ _ _)).
Proof.
  apply TODO.
Defined.

Definition whisker_π₂
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {P₁ P₂ : poly_code}
           {e₁ e₂ : endpoint A Q (P₁ * P₂)}
           (h : homot_endpoint
                  l r
                  al ar
                  e₁
                  e₂)
  : homot_endpoint
      l r
      al ar
      (comp e₁ (π₂ _ _))
      (comp e₂ (π₂ _ _)).
Proof.
  apply TODO.
Defined.

Definition pr1_pair
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {P₁ P₂ : poly_code}
           (e₁ : endpoint A Q P₁)
           (e₂ : endpoint A Q P₂)
  : homot_endpoint
      l r
      al ar
      (comp (pair e₁ e₂) (π₁ _ _))
      e₁.
Proof.
  apply TODO.
Defined.

Definition pr2_pair
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {P₁ P₂ : poly_code}
           (e₁ : endpoint A Q P₁)
           (e₂ : endpoint A Q P₂)
  : homot_endpoint
      l r
      al ar
      (comp (pair e₁ e₂) (π₂ _ _))
      e₂.
Proof.
  apply TODO.
Defined.

Definition comp_pair
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {P₁ P₂ P₃ : poly_code}
           (e₁ : endpoint A Q P₁)
           (e₂ : endpoint A P₁ P₂)
           (e₃ : endpoint A P₁ P₃)
  : homot_endpoint
      l r
      al ar
      (comp e₁ (pair e₂ e₃))
      (pair (comp e₁ e₂) (comp e₁ e₃)).
Proof.
  apply TODO.
Defined.

Definition comp_const
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : one_type}
           (t : T)
           {P : poly_code}
           (e : endpoint A Q P)
  : homot_endpoint
      l r
      al ar
      (comp e (c _ t))
      (c _ t).
Proof.
  apply TODO.
Defined.

Definition fmap_eq
           {A : poly_code}
           {X Y : one_type}
           {f g : X → Y}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {TR : poly_code}
           {al ar : endpoint A (C X) TR}
           (p : f = g)
  : homot_endpoint
      l r
      al ar
      (fmap f)
      (fmap g).
Proof.
  induction p.
  apply refl_e.
Defined.

Section CoequifierSignature.
  Context
    (A B : one_type)
    (f g : A → B)
    (p q : forall (x : A), f x = g x).
  
  Definition no_endpoint
    : ∏ j : ∅, endpoint (C B) (fromempty j) I.
  Proof.
    intro j. induction j.
  Qed.

  (** i (f x) **)
  Definition s_endpoint
    : endpoint (C B) (C A) I
    := comp (fmap f) constr.

  (** i (g x) **)
  Definition t_endpoint
    : endpoint (C B) (C A) I
    := comp (fmap g) constr.

  Definition left_homot_endpoint
    : homot_endpoint
        no_endpoint
        no_endpoint
        (c (C A) (tt : unit_one_type))
        (c (C A) (tt : unit_one_type))
        s_endpoint
        t_endpoint.
  Proof.
    simpl.
    unfold s_endpoint.
    unfold t_endpoint.
    apply ap_constr.
    apply fmap_eq.
    apply funextsec.
    exact p.
  Defined.

  Definition right_homot_endpoint
    : homot_endpoint
        no_endpoint
        no_endpoint
        (c (C A) (tt : unit_one_type))
        (c (C A) (tt : unit_one_type))
        s_endpoint
        t_endpoint.
  Proof.
    simpl.
    unfold s_endpoint.
    unfold t_endpoint.
    apply ap_constr.
    apply fmap_eq.
    apply funextsec.
    exact q.
  Defined.

  Definition coequifier_signature
    : hit_signature.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
    - exact (C B).
    - exact empty.
    - exact fromempty.
    - exact no_endpoint.
    - exact no_endpoint.
    - exact unit.
    - intro. exact (C A).
    - intro. exact (C unit_one_type).
    - intro. exact (c (C A) (tt : unit_one_type)).
    - intro. exact (c (C A) (tt : unit_one_type)).
    - intro. exact s_endpoint.
    - intro. exact t_endpoint.
    - intro. exact left_homot_endpoint.
    - intro. exact right_homot_endpoint.
  Qed.


