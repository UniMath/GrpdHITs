(** Congruence relation of algebras *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Section CongruenceRelation.
  Context {Σ : hit_signature}
          (X : hit_algebra_one_types Σ).

  (** Definition of congruence relation *)
  Definition congruence_relation
    : UU.
  Proof.
    apply TODO.
  Defined.

  (** Projections *)
  Section Projections.
    Variable (R : congruence_relation).

    (** Projections involving the carrier (groupoid structure *)
    Section ProjectionsCarrier.
    End ProjectionsCarrier.

    (** Projections involving the operation (functor) *)
    Section ProjectionsOperation.
    End ProjectionsOperation.

    (** Projections involving the path (natural transformation) *)
    Section ProjectionsPath.
    End ProjectionsPath.

    (** Projections involving the 2-paths (equality) *)
    Section ProjectionsHomot.
    End ProjectionsHomot.
  End Projections.

  Section MakeGroupoidAlgebraFromCongruence.
    Variable (R : congruence_relation).
    
    Definition make_groupoid_algebra_carrier
      : groupoid.
    Proof.
      apply TODO.
    Defined.
    
    Definition make_groupoid_algebra
      : hit_algebra_grpd Σ.
    Proof.
      apply TODO.
    Defined.
  End MakeGroupoidAlgebraFromCongruence.
End CongruenceRelation.
