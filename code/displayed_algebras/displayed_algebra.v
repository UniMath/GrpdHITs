(**
For the induction principle of HITs, we use the notion of displayed algebras.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.

Local Open Scope cat.

(**
Some operations needed to define displayed algebras
 *)
Definition poly_dact_UU
           (P : poly_code)
           {X : UU}
           (Y : X → UU)
  : poly_act P X → UU.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ _, T).
  - exact Y.
  - intro x.
    induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (λ x, IHP₁ (pr1 x) × IHP₂ (pr2 x)).
Defined.

Definition poly_dact_is_one_type
           (P : poly_code)
           {X : one_type}
           (Y : X → UU)
           (Y_is_one_type : ∏ (x : X), isofhlevel 3 (Y x))
  : ∏ (x : poly_act P X), isofhlevel 3 (poly_dact_UU P Y x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ _, one_type_isofhlevel T).
  - exact Y_is_one_type.
  - intro x.
    induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (λ x, isofhleveldirprod 3 _ _ (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Defined.  

Definition poly_dact
           (P : poly_code)
           {X : one_type}
           (Y : X → one_type)
  : poly_act P X → one_type
  := λ x, make_one_type
            (poly_dact_UU P Y x)
            (poly_dact_is_one_type P Y (λ z, one_type_isofhlevel (Y z)) x).

Definition dep_id_fun
           {X : UU}
           {Y : X → UU}
  : ∏ (x : X), Y x → Y x
  := λ _ z, z.

Definition dep_comp_fun
           {A B C : UU}
           {YA : A → UU} {YB : B → UU} {YC : C → UU}
           {f : A → B} {g : B → C}
           (ff : ∏ (a : A), YA a → YB (f a))
           (gg : ∏ (b : B), YB b → YC (g b))
  : ∏ (a : A), YA a → YC (g(f a))
  := λ x z, gg (f x) (ff x z).

Definition dep_inl_fun
           {P Q : poly_code}
           {X : UU}
           {Y : X → UU}
  : ∏ (x : poly_act P X),
    poly_dact_UU P Y x → poly_dact_UU (P + Q) Y (inl x)
  := λ _ z, z.

Definition dep_inr_fun
           {P Q : poly_code}
           {X : UU}
           {Y : X → UU}
  : ∏ (x : poly_act Q X),
    poly_dact_UU Q Y x → poly_dact_UU (P + Q) Y (inr x)
  := λ _ z, z.

Definition dep_pr1_fun
           {P Q : poly_code}
           {X : UU}
           {Y : X → UU}
  : ∏ (x : poly_act (P * Q) X),
    poly_dact_UU (P * Q) Y x → poly_dact_UU P Y (pr1 x)
  := λ _ z, pr1 z.

Definition dep_pr2_fun
           {P Q : poly_code}
           {X : UU}
           {Y : X → UU}
  : ∏ (x : poly_act (P * Q) X),
    poly_dact_UU (P * Q) Y x → poly_dact_UU Q Y (pr2 x)
  := λ _ z, pr2 z.

Definition dep_pair_fun
           {P Q R : poly_code}
           {X : UU}
           {Y : X → UU}
           {f : poly_act P X → poly_act Q X}
           (ff : ∏ (x : poly_act P X),
                 poly_dact_UU P Y x → poly_dact_UU Q Y (f x))
           {g : poly_act P X → poly_act R X}
           (gg : ∏ (x : poly_act P X),
                 poly_dact_UU P Y x → poly_dact_UU R Y (g x))
  : ∏ (x : poly_act P X),
    poly_dact_UU P Y x → poly_dact_UU (Q * R) Y (f x ,, g x)
  := λ x z, ff x z ,, gg x z.

Definition dep_const_fun
           {P : poly_code}
           {X : UU}
           {Y : X → UU}
           {T : one_type}
           (t : T)
  : ∏ (x : poly_act P X),
    poly_dact_UU P Y x → poly_dact_UU (C T) Y t
  := λ _ _, t.

Definition dep_constfun_fun
           {X : UU}
           {Y : X → UU}
           {T₁ T₂ : one_type}
           (f : T₁ → T₂)
  : ∏ (x : poly_act (C T₁) X),
    poly_dact_UU (C T₁) Y x → poly_dact_UU (C T₂) Y (f x)
  := λ _ z, f z.

Definition endpoint_dact_UU
           {A : poly_code}
           {X : UU}
           (c : poly_act A X → X)
           (Y : X → UU)
           {P Q : poly_code}
           (e : endpoint A P Q)
           (cc : ∏ (x : poly_act A X),
                poly_dact_UU A Y x → Y (c x))
  : ∏ {z : poly_act P X},
    poly_dact_UU P Y z
    →
    poly_dact_UU Q Y (sem_endpoint_UU e c z).
Proof.
  induction e as [ | P Q R e₁ IHe₁ e₂ IHe₂ | | | |
                   | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ].
  - exact dep_id_fun.
  - exact (dep_comp_fun IHe₁ IHe₂).
  - exact dep_inl_fun.
  - exact dep_inr_fun.
  - exact dep_pr1_fun.
  - exact dep_pr2_fun.
  - exact (dep_pair_fun IHe₁ IHe₂).
  - exact (dep_const_fun t).
  - exact (dep_constfun_fun f).
  - exact cc.
Defined.

Definition endpoint_dact
           {A : poly_code}
           (X : total_bicat (disp_alg_bicat (⟦ A ⟧)))
           (Y : (pr1 X : one_type) → one_type)
           {P Q : poly_code}
           (e : endpoint A P Q)
           (c : ∏ (x : ⟦ A ⟧ (pr1 X) : one_type),
                poly_dact A Y x → Y (pr2 X x))
  : ∏ {z : (⟦ P ⟧ (pr1 X) : one_type)},
    poly_dact P Y z
    →
    poly_dact Q Y (sem_endpoint_one_types e X z)
  := λ _, endpoint_dact_UU (pr2 X) Y e c.

(** Needed for lifting homotopies *)
Definition PathOver_pr1
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ X × poly_act P₂ X}
           {p : x₁ = x₂}
           {y₁ : poly_dact_UU P₁ Y (pr1 x₁) × poly_dact_UU P₂ Y (pr2 x₁)}
           {y₂ : poly_dact_UU P₁ Y (pr1 x₂) × poly_dact_UU P₂ Y (pr2 x₂)}
  : @PathOver
      _ _ _
      (poly_dact (P₁ * P₂) Y)
      y₁ y₂
      p
    →
    @PathOver
      _ _ _
      (poly_dact P₁ Y)
      (pr1 y₁) (pr1 y₂)
      (maponpaths pr1 p).
Proof.
  induction p.
  exact (λ p, maponpaths pr1 p).
Defined.

Definition PathOver_pr2
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ X × poly_act P₂ X}
           {p : x₁ = x₂}
           {y₁ : poly_dact_UU P₁ Y (pr1 x₁) × poly_dact_UU P₂ Y (pr2 x₁)}
           {y₂ : poly_dact_UU P₁ Y (pr1 x₂) × poly_dact_UU P₂ Y (pr2 x₂)}
  : @PathOver
      _ _ _
      (poly_dact (P₁ * P₂) Y)
      y₁ y₂
      p
    →
    @PathOver
      _ _ _
      (poly_dact P₂ Y)
      (pr2 y₁) (pr2 y₂)
      (maponpaths dirprod_pr2 p).
Proof.
  induction p.
  exact (λ p, maponpaths dirprod_pr2 p).
Defined.

Definition PathOver_pair
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ y₁ : poly_act P₁ X} {x₂ y₂ : poly_act P₂ X}
           {p₁ : x₁ = y₁}
           {p₂ : x₂ = y₂}
           {a₁ : poly_dact_UU P₁ Y x₁} {a₂ : poly_dact_UU P₂ Y x₂}
           {b₁ : poly_dact_UU P₁ Y y₁} {b₂ : poly_dact_UU P₂ Y y₂}
  : @PathOver
      _ x₁ y₁
      (poly_dact P₁ Y)
      a₁ b₁
      p₁
    → @PathOver
        _ x₂ y₂
        (poly_dact P₂ Y)
        a₂ b₂
        p₂
    →
    @PathOver
      _ (x₁ ,, x₂) (y₁ ,, y₂)
      (poly_dact (P₁ * P₂) Y)
      (a₁ ,, a₂) (b₁ ,, b₂)
      (pathsdirprod p₁ p₂).
Proof.
  induction p₁ ; induction p₂.
  exact pathsdirprod.
Defined.

Definition PathOver_inl
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ X}
           {p : x₁ = x₂}
           {y₁ : poly_dact_UU P₁ Y x₁}
           {y₂ : poly_dact_UU P₁ Y x₂}
  : @PathOver
      _ _ _
      (poly_dact P₁ Y)
      y₁ y₂
      p
    →
    @PathOver
      _ (inl x₁) (inl x₂)
      (poly_dact (P₁ + P₂) Y)
      y₁ y₂
      (maponpaths inl p).
Proof.
  induction p.
  exact (λ q, q).
Defined.

Definition PathOver_inr
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₂ X}
           {p : x₁ = x₂}
           {y₁ : poly_dact_UU P₂ Y x₁}
           {y₂ : poly_dact_UU P₂ Y x₂}
  : @PathOver
      _ _ _
      (poly_dact P₂ Y)
      y₁ y₂
      p
    →
    @PathOver
      _ (inr x₁) (inr x₂)
      (poly_dact (P₁ + P₂) Y)
      y₁ y₂
      (maponpaths inr p).
Proof.
  induction p.
  exact (λ q, q).
Defined.

Definition apd_2
           {A B : UU}
           {Y₁ : A → UU}
           {Y₂ : B → UU}
           {c : A → B}
           (cc : ∏ (a : A), Y₁ a → Y₂ (c a))
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           {y₁ : Y₁ a₁} {y₂ : Y₁ a₂}
           (q : PathOver y₁ y₂ p)
  : PathOver
      (cc a₁ y₁)
      (cc a₂ y₂)
      (maponpaths c p).
Proof.
  induction p.
  exact (maponpaths (cc a₁) q).
Defined.

Definition homot_endpoint_dact
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l : ∏ (j : J), endpoint A (S j) I}
           {r : ∏ (j : J), endpoint A (S j) I}
           {X : total_bicat
                  (disp_depprod_bicat
                     J
                     (λ j, add_cell_disp_cat
                             _ _ _
                             (sem_endpoint_one_types (l j))
                             (sem_endpoint_one_types (r j))))}
           {Y : (pr11 X : one_type) → one_type}
           {Q : poly_code}
           {TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : poly_code}
           {sl sr : endpoint A Q T}
           (p : homot_endpoint l r al ar sl sr)
           (c : ∏ (x : ⟦ A ⟧ (pr11 X) : one_type),
                poly_dact A Y x → Y (pr21 X x))
           (pp : ∏ (j : J)
                   (x : poly_act (S j) (pr11 X : one_type))
                   (y : poly_dact (S j) Y x),
                 @PathOver
                   _ _ _
                   Y
                   (endpoint_dact _ Y (l j) c y)
                   (endpoint_dact _ Y (r j) c y)
                   (pr2 X j x))
           {z : poly_act Q (pr11 X : one_type)}
           (zz : poly_dact_UU Q (λ x, Y x) z)
           {p_arg : sem_endpoint_one_types al _ z = sem_endpoint_one_types ar _ z}
           (pp_arg : @PathOver
                       _ _ _
                       (poly_dact TR Y)
                       (endpoint_dact (pr1 X) Y al c zz)
                       (endpoint_dact (pr1 X) Y ar c zz)
                       (sem_homot_endpoint_one_types path_arg (pr1 X) (pr2 X) z p_arg))
  : @PathOver
      _ _ _
      (poly_dact T Y)
      (endpoint_dact (pr1 X) Y sl c zz)
      (endpoint_dact (pr1 X) Y sr c zz)
      (sem_homot_endpoint_one_types p (pr1 X) (pr2 X) _ p_arg).
Proof.
  induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - apply identityPathOver.
  - exact (inversePathOver IHp).
  - exact (composePathOver IHP₁ IHP₂).
  - apply identityPathOver.
  - apply identityPathOver.
  - apply identityPathOver.
  - exact (PathOver_pr1 IHp).
  - exact (PathOver_pr2 IHp).
  - exact (PathOver_pair IHp₁ IHp₂).
  - exact (PathOver_inl IHp).
  - exact (PathOver_inr IHp).
  - apply (pp j).    
  - exact (@apd_2
             _ _ _
             Y _
             c
             _ _
             ((sem_homot_endpoint_one_types p (pr1 X) (pr2 X) z p_arg))
             _ _
             IHp
          ).
  - exact pp_arg.
Defined.

(**
Definition of a displayed algebra
 *)
Definition disp_algebra
           {Σ : hit_signature}
           (X : hit_algebra_one_types Σ)
  : UU
  := ∑ (Y : alg_carrier X → one_type)
       (c : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
            poly_dact (point_constr Σ) Y x → Y (alg_constr X x))
       (pp : ∏ (j : path_label Σ)
               (x : poly_act (path_source Σ j) (alg_carrier X))
               (y : poly_dact (path_source Σ j) Y x),
             @PathOver
               _ _ _
               Y
               (endpoint_dact (pr11 X) Y (path_left Σ j) c y)
               (endpoint_dact (pr11 X) Y (path_right Σ j) c y)
               (alg_path X j x)),
     ∏ (j : homot_label Σ)
       (z : poly_act (homot_point_arg Σ j) (alg_carrier X))
       (zz : poly_dact_UU (homot_point_arg Σ j) Y z)
       (p_arg : sem_endpoint_one_types (homot_path_arg_left Σ j) _ z
                =
                sem_endpoint_one_types (homot_path_arg_right Σ j) _ z)
       (pp_arg : @PathOver
                   _ _ _
                   (poly_dact _ Y)
                   (endpoint_dact (pr11 X) Y (homot_path_arg_left Σ j) c zz)
                   (endpoint_dact (pr11 X) Y (homot_path_arg_right Σ j) c zz)
                   (sem_homot_endpoint_one_types path_arg (pr11 X) (pr21 X) z p_arg)),
     globe_over
       Y
       (pr2 X j z p_arg)
       (homot_endpoint_dact (homot_left_path Σ j) c pp zz pp_arg)
       (homot_endpoint_dact (homot_right_path Σ j) c pp zz pp_arg).

(**
Projections
 *)
Definition disp_algebra_type_family
           {Σ : hit_signature}
           {X : hit_algebra_one_types Σ}
           (Y : disp_algebra X)
  : alg_carrier X → UU
  := pr1 Y.

Coercion disp_algebra_type_family : disp_algebra >-> Funclass.

Section DispAlgebraProjections.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}.
  Variable (Y : disp_algebra X).

  Definition disp_alg_constr
    : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
      poly_dact (point_constr Σ) (pr1 Y) x
      →
      pr1 Y (alg_constr X x)
    := pr12 Y.

  Definition disp_alg_path
    : ∏ (j : path_label Σ)
        (x : poly_act (path_source Σ j) (alg_carrier X))
        (y : poly_dact (path_source Σ j) (pr1 Y) x),
      @PathOver
        _ _ _
        Y
        (endpoint_dact (pr11 X) (pr1 Y) (path_left Σ j) (pr12 Y) y)
        (endpoint_dact (pr11 X) (pr1 Y) (path_right Σ j) (pr12 Y) y) 
        (alg_path X j x)
    := pr122 Y.

  Definition disp_alg_homot
    :  ∏ (j : homot_label Σ)
         (z : poly_act (homot_point_arg Σ j) (alg_carrier X))
         (zz : poly_dact_UU (homot_point_arg Σ j) Y z)
         (p_arg : (sem_endpoint_one_types (homot_path_arg_left Σ j)) (pr11 X) z
                  =
                  (sem_endpoint_one_types (homot_path_arg_right Σ j)) (pr11 X) z)
         (pp_arg : @PathOver
                     _ _ _
                     (poly_dact _ (pr1 Y))
                     (endpoint_dact
                        (pr11 X) (pr1 Y)
                        (homot_path_arg_left Σ j) (pr12 Y) zz)
                     (endpoint_dact
                        (pr11 X) (pr1 Y)
                        (homot_path_arg_right Σ j) (pr12 Y) zz)
                     (sem_homot_endpoint_one_types path_arg (pr11 X) (pr21 X) z p_arg)),
       globe_over
         Y
         (pr2 X j z p_arg)
         (homot_endpoint_dact
            (homot_left_path Σ j) 
            (pr12 Y) (pr122 Y) zz pp_arg)
         (homot_endpoint_dact
            (homot_right_path Σ j) 
            (pr12 Y) (pr122 Y) zz pp_arg)
    := pr222 Y.
End DispAlgebraProjections.

(**
Builder
 *)
Definition make_disp_algebra
           {Σ : hit_signature}
           {X : hit_algebra_one_types Σ}
           (Y : alg_carrier X → one_type)
           (c : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
                poly_dact (point_constr Σ) Y x
                →
                Y (alg_constr X x))
           (p : ∏ (j : path_label Σ)
                  (x : poly_act (path_source Σ j) (alg_carrier X))
                  (y : poly_dact (path_source Σ j) Y x),
                @PathOver
                  _ _ _
                  Y
                  (endpoint_dact (pr11 X) Y (path_left Σ j) c y)
                  (endpoint_dact (pr11 X) Y (path_right Σ j) c y) 
                  (alg_path X j x))
           (h : ∏ (j : homot_label Σ)
                  (z : poly_act (homot_point_arg Σ j) (alg_carrier X))
                  (zz : poly_dact_UU (homot_point_arg Σ j) Y z)
                  (p_arg : (sem_endpoint_one_types
                              (homot_path_arg_left Σ j)) (pr11 X) z
                           =
                           (sem_endpoint_one_types
                              (homot_path_arg_right Σ j)) (pr11 X) z)
                  (pp_arg : @PathOver
                              _ _ _
                              (poly_dact _ Y)
                              (endpoint_dact
                                 (pr11 X) Y
                                 (homot_path_arg_left Σ j) c zz)
                              (endpoint_dact
                                 (pr11 X) Y
                                 (homot_path_arg_right Σ j) c zz)
                              (sem_homot_endpoint_one_types
                                 path_arg (pr11 X) (pr21 X) z p_arg)),
                globe_over
                  Y
                  (pr2 X j z p_arg)
                  (homot_endpoint_dact
                     (homot_left_path Σ j) 
                     c p zz pp_arg)
                  (homot_endpoint_dact
                     (homot_right_path Σ j) 
                     c p zz pp_arg))
  : disp_algebra X
  := (Y ,, (c ,, (p ,, h))).

(**
Operation necessary to define sections
 *)
Definition poly_dmap
           (P : poly_code)
           {X : UU}
           (Y : X → UU)
           (f : ∏ (x : X), Y x)
  : ∏ (x : poly_act P X), poly_dact_UU P Y x.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idfun T).
  - exact f.
  - intros x.
    induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (λ x, IHP₁ (pr1 x) ,, IHP₂ (pr2 x)).
Defined.

(**
Maps to a displayed algebra (sections of the display map)
 *)
Definition endpoint_dact_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           {Y : (pr1 X : one_type) → one_type}
           {f : ∏ (x : pr1 X : one_type), Y x}
           {c : ∏ (x : poly_act A (pr1 X : one_type)),
                poly_dact A Y x
                →
                Y (pr2 X x)}
           (cf : ∏ (x : poly_act A (pr1 X : one_type)),
                 f (pr2 X x)
                 =
                 c x (poly_dmap A Y f x))
           (x : poly_act P (pr1 X : one_type))
  : poly_dmap Q Y f ((sem_endpoint_one_types e) X x)
    =
    endpoint_dact
      X Y e c
      (poly_dmap P Y f x).
Proof.
  induction e as [ | P Q R e₁ IHe₁ e₂ IHe₂ | | | |
                   | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - apply idpath.
  - exact (IHe₂ _ @ maponpaths _ (IHe₁ x)).
  - apply idpath.
  - apply idpath.
  - apply idpath.
  - apply idpath.
  - exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  - apply idpath.
  - apply idpath.
  - exact (cf x).
Defined.

Definition PathOver_square
           {A : UU}
           (Y : A → UU)
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           (h : p₁ = p₂)
           {y₁ z₁ : Y a₁}
           {y₂ z₂ : Y a₂}
           (q₁ : PathOver y₁ y₂ p₁)
           (q₂ : PathOver z₁ z₂ p₂)
           (s₁ : y₁ = z₁)
           (s₂ : y₂ = z₂)
  : UU.
Proof.
  induction s₁, s₂, h.
  exact (q₁ = q₂).
Defined.

Definition disp_algebra_map
           {Σ : hit_signature}
           {X : hit_algebra_one_types Σ}
           (Y : disp_algebra X)
  : UU
  := ∑ (f : ∏ (x : alg_carrier X), Y x)
       (cf : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
             f (alg_constr X x)
             =
             disp_alg_constr Y x (poly_dmap (point_constr Σ) (pr1 Y) f x)),
     ∏ (j : path_label Σ)
       (x : poly_act (path_source Σ j) (alg_carrier X)),
     PathOver_square
       _
       (idpath _)
       (apd f (alg_path X j x))
       (disp_alg_path Y j x (poly_dmap (path_source Σ j) (pr1 Y) f x))
       (endpoint_dact_natural (path_left Σ j) cf x)
       (endpoint_dact_natural (path_right Σ j) cf x).
