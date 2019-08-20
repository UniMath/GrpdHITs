(** Here we define W-types of polynomials *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import signature.hit_signature.

Local Definition TODO {A : UU} : A.
Admitted.

(** Basics of containers *)
Record container :=
  mkContainer
    {
      shapes : UU ;
      positions : shapes → UU
    }.

(** Builder *)
Definition make_container
           (S : UU)
           (P : S → UU)
  : container.
Proof.
  use mkContainer.
  - exact S.
  - exact P.
Defined.

Notation "S ◅ P" := (make_container S P) (at level 70) : container_scope.

Local Open Scope container_scope.

(** Constructions of containers *)
Definition constant_container
           (A : UU)
  : container
  := A ◅ (λ _, ∅).

Definition identity_container
  : container
  := unit ◅ (λ _, unit).

Definition sum_container
           (C₁ C₂ : container)
  : container
  := (shapes C₁ ⨿ shapes C₂) ◅ (coprod_rect _ (positions C₁) (positions C₂)).

Definition prod_container
           (C₁ C₂ : container)
  : container
  := (shapes C₁ × shapes C₂) ◅ (λ z, positions C₁ (pr1 z) ⨿ positions C₂ (pr2 z)).

Definition poly_container
           (P : poly_code)
  : container.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (constant_container A).
  - exact identity_container.
  - exact (sum_container IHP₁ IHP₂).
  - exact (prod_container IHP₁ IHP₂).
Defined.

(** Interpretation of containers *)
Definition interpret_container
           (C : container)
           (X : UU)
  : UU
  := ∑ (s : shapes C), positions C s → X.

Notation "⟦ C ⟧ X" := (interpret_container C X) (at level 70) : container_scope.

Definition cpair
           (C : container)
           {X : UU}
           (s : shapes C)
           (p : positions C s → X)
  : ⟦ C ⟧ X
  := s ,, p.

Definition interpret_map
           (C : container)
           {X Y : UU}
           (f : X → Y)
  : ⟦ C ⟧ X → ⟦ C ⟧ Y
  := λ z, cpair C (pr1 z) (λ q, f (pr2 z q)).

Definition interpret_map_id
           (C : container)
           (X : UU)
           (x : ⟦ C ⟧ X)
  : interpret_map C (idfun X) x = x
  := idpath _.

Definition interpret_map_comp
           (C : container)
           {X Y Z : UU}
           (f : X → Y) (g : Y → Z)
           (x : ⟦ C ⟧ X)
  : interpret_map C (λ z, g(f z)) x
    =
    interpret_map C g (interpret_map C f x)
  := idpath _.

(** Interpretation of the constructions (up to equivalence) *)

(** Constant *)
Definition interpret_constant
           (A : UU)
           (X : UU)
  : ⟦ constant_container A ⟧ X → A
  := λ z, pr1 z.

Definition to_interpret_constant
           (A : UU)
           (X : UU)
  : A → ⟦ constant_container A ⟧ X
  := λ a, a ,, fromempty.

Definition interpret_constant_weq
           (A : UU)
           (X : UU)
  : ⟦ constant_container A ⟧ X ≃ A.
Proof.
  use make_weq.
  - exact (interpret_constant A X).
  - use gradth.
    + exact (to_interpret_constant A X).
    + intros x.
      use total2_paths_f.
      * exact (idpath _).
      * use funextsec.
        intro z ; induction z.
    + intros x.
      apply idpath.
Defined.

(** Identity *)
Definition interpret_identity
           (X : UU)
  : ⟦ identity_container ⟧ X → X
  := λ z, pr2 z tt.

Definition to_interpret_identity
           (X : UU)
  : X → ⟦ identity_container ⟧ X
  := λ z, tt ,, (λ _, z).

Definition interpret_identity_weq
           (X : UU)
  : ⟦ identity_container ⟧ X ≃ X.
Proof.
  use make_weq.
  - exact (interpret_identity X).
  - use gradth.
    + exact (to_interpret_identity X).
    + intros x.
      induction x as [sx px].
      induction sx.
      apply (maponpaths (λ z, tt ,, z)).
      use funextsec.
      intro z.
      induction z.
      apply idpath.
    + intro y.
      apply idpath.
Defined.

(** Sum *)
Definition interpret_sum
           (C₁ C₂ : container)
           (X : UU)
  : ⟦ sum_container C₁ C₂ ⟧ X
    →
    (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X).
Proof.
  intros z.
  induction z as [sz pz].
  induction sz as [sz | sz].
  + exact (inl (sz ,, pz)).
  + exact (inr (sz ,, pz)).
Defined.

Definition to_interpret_sum
           (C₁ C₂ : container)
           (X : UU)
  : (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X)
    →
    ⟦ sum_container C₁ C₂ ⟧ X.
Proof.
  intros z.
  induction z as [z | z].
  - exact (inl (pr1 z) ,, pr2 z).
  - exact (inr (pr1 z) ,, pr2 z).
Defined.

Definition interpret_sum_weq
           (C₁ C₂ : container)
           (X : UU)
  : ⟦ sum_container C₁ C₂ ⟧ X
    ≃
    (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X).
Proof.
  use make_weq.
  - exact (interpret_sum C₁ C₂ X).
  - use gradth.
    + exact (to_interpret_sum C₁ C₂ X).
    + intro z.
      induction z as [sz pz].
      induction sz as [sz | sz].
      * apply idpath.
      * apply idpath.
    + intros z.
      induction z as [z | z].
      * apply idpath.
      * apply idpath.
Defined.

(** The product *)
Definition interpret_prod
           (C₁ C₂ : container)
           (X : UU)
  : ⟦ prod_container C₁ C₂ ⟧ X
    →
    (⟦ C₁ ⟧ X) × (⟦ C₂ ⟧ X).
Proof.
  intros z.
  refine ((pr11 z ,, _) ,, (pr21 z ,, _)).
  - exact (λ q, pr2 z (inl q)).
  - exact (λ q, pr2 z (inr q)).
Defined.

Definition to_interpret_prod
           (C₁ C₂ : container)
           (X : UU)
  : (⟦ C₁ ⟧ X) × (⟦ C₂ ⟧ X)
    →
    ⟦ prod_container C₁ C₂ ⟧ X
  := λ z, (pr11 z ,, pr12 z) ,, coprod_rect _ (λ q, pr21 z q) (λ q, pr22 z q).

Definition interpret_prod_weq
           (C₁ C₂ : container)
           (X : UU)
  : ⟦ prod_container C₁ C₂ ⟧ X
    ≃
    (⟦ C₁ ⟧ X) × (⟦ C₂ ⟧ X).
Proof.
  use make_weq.
  - exact (interpret_prod C₁ C₂ X).
  - use gradth.
    + exact (to_interpret_prod C₁ C₂ X).
    + intro z.
      use total2_paths_f.
      * apply idpath.
      * use funextsec.
        intro q.
        induction q.
        ** apply idpath.
        ** apply idpath.
    + intros z.
      apply idpath.
Defined.

(** Polynomials *)
Definition interpret_poly
           (P : poly_code)
           (X : UU)
  : ⟦ poly_container P ⟧ X
    →
    poly_act P X.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply interpret_constant.
  - apply interpret_identity.
  - intro z.
    induction (interpret_sum (poly_container P₁) (poly_container P₂) X z) as [q | q].
    + exact (inl (IHP₁ q)).
    + exact (inr (IHP₂ q)).
  - intro z.
    pose (interpret_prod (poly_container P₁) (poly_container P₂) X z) as q.
    exact (IHP₁ (pr1 q) ,, IHP₂ (pr2 q)).
Defined.

Definition to_interpret_poly
           (P : poly_code)
           (X : UU)
  : poly_act P X
    →
    ⟦ poly_container P ⟧ X.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply to_interpret_constant.
  - apply to_interpret_identity.
  - intro z.
    induction z as [z | z].
    + exact (to_interpret_sum
               (poly_container P₁) (poly_container P₂) X
               (inl (IHP₁ z))).
    + exact (to_interpret_sum
               (poly_container P₁) (poly_container P₂) X
               (inr (IHP₂ z))).
  - exact (λ z, to_interpret_prod
                  (poly_container P₁) (poly_container P₂) X
                  (IHP₁ (pr1 z) ,, IHP₂ (pr2 z))).
Defined.

Definition to_interpret_poly_interpret_poly
           (P : poly_code)
           (X : UU)
           (x : ⟦ poly_container P ⟧ X)
  : to_interpret_poly P X (interpret_poly P X x) = x.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
Defined.

Definition interpret_poly_to_interpret_poly
           (P : poly_code)
           (X : UU)
           (y : poly_act P X)
  : interpret_poly P X (to_interpret_poly P X y) = y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply TODO.
  - apply TODO.
  - apply TODO.
  - apply TODO.
Defined.

Definition interpret_poly_weq
           (P : poly_code)
           (X : UU)
  : ⟦ poly_container P ⟧ X
    ≃
    poly_act P X.
Proof.
  use make_weq.
  - exact (interpret_poly P X).
  - use gradth.
    + exact (to_interpret_poly P X).
    + exact (to_interpret_poly_interpret_poly P X).
    + exact (interpret_poly_to_interpret_poly P X).
Defined.

(** W-types for containers *)
Inductive W (C : container) : UU :=
| sup : ⟦ C ⟧ (W C) → W C.

Fixpoint W_rec_map
         (C : container)
         (Y : UU)
         (fY : ⟦ C ⟧ Y → Y)
         (z : W C)
  : Y
  := match z with
     | sup _ f => fY (cpair
                        C
                        (pr1 f)
                        (λ p, W_rec_map C Y fY (pr2 f p)))
     end.

Definition W_rec_comp
           (C : container)
           (Y : UU)
           (fY : ⟦ C ⟧ Y → Y)
           (z : ⟦ C ⟧ (W C))
  : W_rec_map C Y fY (sup C z) = fY (interpret_map C (W_rec_map C Y fY) z)
  := idpath _.

(** W-types for polynomials *)
Definition poly_initial
           (P : poly_code)
  : UU
  := W (poly_container P).

Definition poly_initial_alg
           (P : poly_code)
  : poly_act P (poly_initial P) → poly_initial P
  := λ z, sup (poly_container P) (to_interpret_poly P _ z).

Definition poly_initial_rec
           (P : poly_code)
           (Y : UU)
           (fY : poly_act P Y → Y)
           (z : poly_initial P)
  : Y
  := W_rec_map
       (poly_container P) Y
       (λ q, fY (interpret_poly P Y q))
       z.

Definition poly_initial_comp
           (P : poly_code)
           (Y : UU)
           (fY : poly_act P Y → Y)
           (z : poly_act P (poly_initial P))
  : poly_initial_rec
      P Y fY
      (poly_initial_alg P z)
    =
    fY (poly_map P (poly_initial_rec P Y fY) z).
Proof.
  refine (W_rec_comp
            (poly_container P) Y (λ q, fY (interpret_poly P Y q))
            _
          @
          maponpaths
            fY
            _
         ).
  apply TODO.
Defined.
