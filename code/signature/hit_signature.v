(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.

(**
Data type of polynomials.
These are used for both the point constructor and the arguments of the path constructors.
 *)
Inductive poly_code : UU :=
| C : one_type → poly_code
| I : poly_code
| plus : poly_code → poly_code → poly_code
| times : poly_code → poly_code → poly_code.

Notation "P + Q" := (plus P Q).
Notation "P * Q" := (times P Q).

(** Action of polynomials on the universe *)
Definition poly_act
           (P : poly_code)
           (X : UU)
  : UU.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact A.
  - exact X.
  - exact (IHP₁ ⨿ IHP₂).
  - exact (IHP₁ × IHP₂).
Defined.

Definition poly_map
           (P : poly_code)
           {X Y : UU}
           (f : X → Y)
  : poly_act P X → poly_act P Y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ a, a).
  - exact f.
  - exact (coprodf IHP₁ IHP₂).
  - exact (dirprodf IHP₁ IHP₂).
Defined.

(**
Type of endpoints
 *)
Inductive endpoint (A : poly_code) : poly_code → poly_code → UU :=
| id_e : forall (P : poly_code), endpoint A P P
| comp : forall (P Q R : poly_code), endpoint A P Q → endpoint A Q R → endpoint A P R
| ι₁ : forall (P Q : poly_code), endpoint A P (P + Q)
| ι₂ : forall (P Q : poly_code), endpoint A Q (P + Q)
| π₁ : forall (P Q : poly_code), endpoint A (P * Q) P
| π₂ : forall (P Q : poly_code), endpoint A (P * Q) Q
| pair : forall (P Q R : poly_code),
    endpoint A P Q -> endpoint A P R → endpoint A P (Q * R)
| c : forall (P : poly_code) (T : one_type), T → endpoint A P (C T)
| fmap : forall {X Y : one_type} (f : X → Y), endpoint A (C X) (C Y)
| constr : endpoint A A I.

Arguments id {_} _.
Arguments comp {A} {P} {Q} {R} _ _.
Arguments ι₁ {_} P Q.
Arguments ι₂ {_} P Q.
Arguments π₁ {_} P Q.
Arguments π₂ {_} P Q.
Arguments pair {A} {P} {Q} {R} _ _.
Arguments c {_} P {_} _.
Arguments fmap {_} {X Y} f.
Arguments constr {_}.
