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
           {X : one_type}
           (Y : X → UU)
  : (⟦ P ⟧ X : one_type) → UU.
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
  : ∏ (x : ⟦ P ⟧ X : one_type), isofhlevel 3 (poly_dact_UU P Y x).
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
  : (⟦ P ⟧ X : one_type) → one_type
  := λ x, make_one_type
            (poly_dact_UU P Y x)
            (poly_dact_is_one_type P Y (λ z, one_type_isofhlevel (Y z)) x).

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
    poly_dact Q Y (sem_endpoint_one_types e X z).
Proof.
  induction e as [ | P Q R e₁ IHe₁ e₂ IHe₂ | | | |
                   | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ].
  - exact (λ z, idfun _).
  - exact (λ z x, IHe₂ (sem_endpoint_one_types e₁ X z) (IHe₁ z x)).
  - exact (λ z, idfun _).
  - exact (λ z, idfun _).
  - exact (λ z, pr1).
  - exact (λ z, pr2).
  - exact (λ z x, (IHe₁ z x ,, IHe₂ z x)).
  - exact (λ _ _, t).
  - exact (λ z Hz, f Hz).
  - exact c.
Defined.

(*
(**
Definition of a displayed algebra
 *)
Definition disp_algebra
           {Σ : hit_signature}
           (X : set_algebra Σ)
  : UU
  :=
    ∑ (Y : alg_carrier X → hSet)
      (c : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
           poly_dact (point_arg Σ) Y x → Y (alg_operation X x)),
    ∏ (j : path_index Σ)
      (x : ⦃ path_arg Σ j ⦄ (alg_carrier X))
      (y : poly_dact (path_arg Σ j) Y x),
    transportf
      (poly_dact I Y)
      (alg_paths X j x)
      (endpoint_dact (alg_to_prealg X) (path_lhs Σ j) c y)
    =
    endpoint_dact (alg_to_prealg X) (path_rhs Σ j) c y.

(**
Projections
 *)
Definition disp_algebra_type_family
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : disp_algebra X)
  : alg_carrier X → hSet
  := pr1 Y.

Coercion disp_algebra_type_family : disp_algebra >-> Funclass.

Section DispAlgebraProjections.
  Context {Σ : hit_signature}
          {X : set_algebra Σ}.
  Variable (Y : disp_algebra X).

  Definition disp_alg_operation
    : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
      poly_dact (point_arg Σ) Y x → Y (alg_operation X x)
    := pr12 Y.

  Definition disp_alg_paths
    : ∏ (j : path_index Σ)
        (x : ⦃ path_arg Σ j ⦄ (alg_carrier X))
        (y : poly_dact (path_arg Σ j) Y x),
      transportf
        (poly_dact I Y)
        (alg_paths X j x)
        (endpoint_dact (alg_to_prealg X) (path_lhs Σ j) disp_alg_operation y)
      =
      endpoint_dact (alg_to_prealg X) (path_rhs Σ j) disp_alg_operation y
  := pr22 Y.
End DispAlgebraProjections.

(**
Builder
 *)
Definition make_disp_algebra
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : alg_carrier X → hSet)
           (c : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
                poly_dact (point_arg Σ) Y x → Y (alg_operation X x))
           (p : ∏ (j : path_index Σ)
                  (x : ⦃ path_arg Σ j ⦄ (alg_carrier X))
                  (y : poly_dact (path_arg Σ j) Y x),
                transportf
                  (poly_dact I Y)
                  (alg_paths X j x)
                  (endpoint_dact (alg_to_prealg X) (path_lhs Σ j) c y)
                =
                endpoint_dact (alg_to_prealg X) (path_rhs Σ j) c y)
  : disp_algebra X
  := (Y ,, (c ,, p)).

(**
Operation necessary to define sections
 *)
Definition poly_dmap
           (P : poly_code)
           {X : hSet}
           (Y : X → hSet)
           (f : ∏ (x : X), Y x)
  : ∏ (x : ⦃ P ⦄ X), poly_dact P Y x.
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
Definition disp_algebra_map
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : disp_algebra X)
  : UU
  := ∑ (f : ∏ (x : alg_carrier X), Y x),
     ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
     f (alg_operation X x)
     =
     disp_alg_operation Y x (poly_dmap (point_arg Σ) Y f x).
*)
