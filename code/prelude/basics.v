(** Here we collect miscellaneous results we need. *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Definition empty_one_type
  : one_type
  := make_one_type ∅ (hlevelntosn _ _ (hlevelntosn _ _ isapropempty)).

Definition unit_one_type
  : one_type
  := make_one_type unit (hlevelntosn _ _ (hlevelntosn _ _ isapropunit)).

(** General lemmata involving paths *)
Definition paths_pathsdirprod
           {A B : UU}
           {a₁ a₂ : A} {b₁ b₂ : B}
           {p₁ p₂ : a₁ = a₂} {q₁ q₂ : b₁ = b₂}
           (s₁ : p₁ = p₂) (s₂ : q₁ = q₂)
  : pathsdirprod p₁ q₁ = pathsdirprod p₂ q₂.
Proof.
  induction s₁, s₂.
  apply idpath.
Defined.

Definition maponpaths_paths
           {A B : UU}
           {f g : A → B}
           (h : ∏ (x : A), f x = g x)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : maponpaths f (!p) @ h a₁ @ maponpaths g p = h a₂.
Proof.
  induction p.
  apply pathscomp0rid.
Defined.

Definition maponpaths_paths'
           {A B : UU}
           {f g : A → B}
           (h : ∏ (x : A), f x = g x)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : h a₁ @ maponpaths g p = maponpaths f p @ h a₂.
Proof.
  induction p.
  apply pathscomp0rid.
Defined.

Definition homotsec_natural
           {A B : UU}
           {f g : A → B}
           (e : f ~ g)
           {a₁ a₂ : A}
           (p : a₂ = a₁)
  : e a₁ = maponpaths f (!p) @ e a₂ @ maponpaths g p.
Proof.
  induction p.
  exact (!(pathscomp0rid _)).
Defined.

Definition homotsec_natural'
           {A B : UU}
           {f g : A → B}
           (e : f ~ g)
           {a₁ a₂ : A}
           (p : a₂ = a₁)
  : maponpaths f p @ e a₁ = e a₂ @ maponpaths g p.
Proof.
  induction p.
  exact (!(pathscomp0rid _)).
Defined.

Definition homotsec2_natural
           {A B C : UU}
           {f g : A → B → C}
           (e : ∏ (a : A) (b : B), f a b = g a b)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           {b₁ b₂ : B}
           (q : b₁ = b₂)
  : e a₁ b₁
    @ maponpaths (λ z, g (pr1 z) (pr2 z)) (pathsdirprod p q)
    =
    maponpaths (λ z, f (pr1 z) (pr2 z)) (pathsdirprod p q)
    @ e a₂ b₂.
Proof.
  induction p ; induction q.
  apply pathscomp0rid.
Defined.

Definition homotsec2_natural_inv
           {A B C : UU}
           {f g : A → B → C}
           (e : ∏ (a : A) (b : B), f a b = g a b)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           {b₁ b₂ : B}
           (q : b₁ = b₂)
  : maponpaths (λ z, g (pr1 z) (pr2 z)) (pathsdirprod p q)
    @ ! e a₂ b₂
    =
    ! e a₁ b₁
    @ maponpaths (λ z, f (pr1 z) (pr2 z)) (pathsdirprod p q).
Proof.
  induction p ; induction q.
  exact (!(pathscomp0rid _)).
Defined.

Definition pathscomp0lid
           {A : UU}
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : idpath a₁ @ p = p
  := idpath p.

Definition maponpaths_pr1_pathsdirprod
           {A B : UU}
           {a₁ a₂ : A}
           {b₁ b₂ : B}
           (p : a₁ = a₂)
           (q : b₁ = b₂)
  : maponpaths pr1 (pathsdirprod p q) = p.
Proof.
  induction p, q.
  apply idpath.
Defined.

Definition maponpaths_pr2_pathsdirprod
           {A B : UU}
           {a₁ a₂ : A}
           {b₁ b₂ : B}
           (p : a₁ = a₂)
           (q : b₁ = b₂)
  : maponpaths dirprod_pr2 (pathsdirprod p q) = q.
Proof.
  induction p, q.
  apply idpath.
Defined.

Definition maponpaths_pathsdirprod_precompose
           {A₁ A₂ B₁ B₂ C : UU}
           (f : A₂ → B₂ → C)
           (g₁ : A₁ → A₂)
           (g₂ : B₁ → B₂)
           {x₁ x₂ : A₁} (p : x₁ = x₂)
           {y₁ y₂ : B₁} (q : y₁ = y₂)
  : maponpaths
      (λ z, f (g₁ (pr1 z)) (g₂ (pr2 z)))
      (pathsdirprod p q)
    =
    maponpaths
      (λ z, f (pr1 z) (pr2 z))
      (pathsdirprod
         (maponpaths g₁ p)
         (maponpaths g₂ q)).
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.

Definition maponpaths_make_dirprod_left
           {A B : UU}
           (a : A)
           {b₁ b₂ : B}
           (p : b₁ = b₂)
  : maponpaths (λ z, a ,, z) p
    =
    pathsdirprod (idpath a) p.
Proof.
  induction p.
  apply idpath.  
Defined.

Definition maponpaths_make_dirprod_right
           {A B : UU}
           (a : A)
           {b₁ b₂ : B}
           (p : b₁ = b₂)
  : maponpaths (λ z, z ,, a) p
    =
    pathsdirprod p (idpath a).
Proof.
  induction p.
  apply idpath.  
Defined.

Definition pathsdirprod_inv
           {A B : UU}
           {a₁ a₂ : A} {b₁ b₂ : B}
           (p : a₁ = a₂) (q : b₁ = b₂)
  : ! pathsdirprod p q = pathsdirprod (!p) (!q).
Proof.
  induction p ; induction q.
  apply idpath.
Defined.

(** The diagonal of a function with two arguments. *)
Definition diag2
           {X Z : UU}
           (f : X → X → Z)
  : X → Z
  := λ x, f x x.

(** `ap` on the diagonal of a function. *)
Definition ap_diag2
           {X Z : UU}
           (f : X → X → Z)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
  : maponpaths (diag2 f) p
    =
    maponpaths (λ z, f x₁ z) p @ maponpaths (λ z, f z x₂) p.
Proof.
  induction p.
  exact (idpath _).
Defined.

(** Curries a function on a product. *)
Definition curry
           {X Y Z : UU}
           (f : X × Y → Z)
  : X → Y → Z
  := λ x y, f (x ,, y).

(** `ap` on an uncurried function. *)
Definition uncurry_ap
           {X Y Z : UU}
           (f : X → Y → Z)
           {x₁ x₂ : X} {y₁ y₂ : Y}
           (p : x₁ = x₂) (q : y₁ = y₂)
  : maponpaths (uncurry f) (pathsdirprod p q)
    =
    maponpaths (λ z, f z y₁) p @ maponpaths (f x₂) q.
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.

(** `ap` on a curried function. *)
Definition curry_ap
           {X Y Z : UU}
           (f : X × Y → Z)
           {x₁ x₂ : X × Y}
           (p : x₁ = x₂)
  : maponpaths f p
    =
    (maponpaths (λ z, curry f z (pr2 x₁)) (maponpaths pr1 p))
      @
      maponpaths (λ z, curry f (pr1 x₂) z) (maponpaths dirprod_pr2 p).
Proof.
  induction p.
  apply idpath.
Defined.

(** `ap` on `λx.(x,y)` with `y` constant. *)
Definition ap_pair_l
           {X Y : UU}
           {x₁ x₂ : X} (y : Y)
           (p : x₁ = x₂)
  : maponpaths (λ x, (x ,, y)) p = pathsdirprod p (idpath y).
Proof.
  induction p.
  apply idpath.
Defined.

(** `ap` on `λy.(x,y)` with `x` constant. *)
Definition ap_pair_r
           {X Y : UU}
           (x : X) {y₁ y₂ : Y}
           (q : y₁ = y₂)
  : maponpaths (λ y, x ,, y) q = pathsdirprod (idpath x) q.
Proof.
  induction q.
  apply idpath.
Defined.

(** Univalence for n-types *)
Definition HLevel_to_UU
           {n : nat}
           (A : HLevel n)
  : UU.
Proof.
  apply A.
Defined.

Definition path_HLevel
           {n : nat}
           {A B : HLevel n}
           (f : HLevel_to_UU A ≃ HLevel_to_UU B)
  : A = B
  := invmap (UA_for_HLevels n A B) f.

Definition path_HLevel_id
           {n : nat}
           (A : HLevel n)
  : path_HLevel (idweq (HLevel_to_UU A)) = idpath _.
Proof.
  apply invmap_eq.
  apply idpath.
Defined.

Definition UA_for_HLevels_concat
           {n : nat}
           {A B C : HLevel n}
           (p : A = B) (q : B = C)
  : UA_for_HLevels n A C (p @ q)
    =
    weqcomp (UA_for_HLevels n A B p) (UA_for_HLevels n B C q).
Proof.
  induction p.
  induction q.
  use subtypePath.
  { intro ; apply isapropisweq. }
  apply idpath.
Defined.

Definition path_HLevel_comp
           {n : nat}
           {A B C : HLevel n}
           (f : HLevel_to_UU A ≃ HLevel_to_UU B)
           (g : HLevel_to_UU B ≃ HLevel_to_UU C)
  : path_HLevel (weqcomp f g)
    =
    path_HLevel f @ path_HLevel g.
Proof.
  apply invmap_eq.
  rewrite UA_for_HLevels_concat.
  unfold path_HLevel.
  rewrite !homotweqinvweq.
  apply idpath.
Qed.

Definition UA_for_HLevels_inv
           {n : nat}
           {A B : HLevel n}
           (p : A = B)
  : UA_for_HLevels n B A (! p)
    =
    invweq (UA_for_HLevels n A B p).
Proof.
  induction p.
  use subtypePath.
  { intro ; apply isapropisweq. }
  apply idpath.
Defined.

Definition path_HLevel_inv
           {n : nat}
           {A B : HLevel n}
           (f : HLevel_to_UU A ≃ HLevel_to_UU B)
  : path_HLevel (invweq f) = !(path_HLevel f).
Proof.
  apply invmap_eq.
  rewrite UA_for_HLevels_inv.
  unfold path_HLevel.
  rewrite !homotweqinvweq.
  apply idpath.
Qed.

Definition path_HLevel_eq
           {n : nat}
           {A B : HLevel n}
           (f g : HLevel_to_UU A ≃ HLevel_to_UU B)
           (p : ∏ x, pr1 f x = pr1 g x)
  : path_HLevel f = path_HLevel g.
Proof.
  apply maponpaths.
  use subtypePath.
  { intro ; apply isapropisweq. }
  use funextsec.
  intro.
  exact (p x).
Qed.

(** The analogue of `transport_idmap_ap` for `hSets. *)
Definition transport_idmap_ap_set
           {A : UU}
           (P : A → hSet)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (u : P a₁)
  : transportf P p u
    =
    transportf (λ (X : hSet), X) (maponpaths P p) u.
Proof.
  induction p.
  apply idpath.
Defined.

Definition UA_for_HLevels_is_transportf
           {A B : hSet}
           (p : A = B)
           (x : A)
  : UA_for_HLevels 2 A B p x
    =
    transportf (λ (X : hSet), pr1hSet X) p x.
Proof.
  induction p.
  apply idpath.
Defined.

(** The analogue of `transport_path_universe` for `hSet`. *) 
Definition transport_path_hset
           {A B : hSet}
           (f : A ≃ B)
           (u : A)
  : transportf (λ (X : hSet), X) (@path_HLevel 2 _ _ f) u
    =
    f u.
Proof.
  rewrite <- UA_for_HLevels_is_transportf.
  unfold path_HLevel.
  exact (eqtohomot (maponpaths pr1 (homotweqinvweq (UA_for_HLevels 2 A B) f)) u).
Defined.
