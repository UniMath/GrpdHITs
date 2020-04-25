(** The first isomorphism theorem for algebras *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.one_types_adjoint_equivalence.
Require Import existence.initial_algebra.
Require Import isomorphism_theorem.congruence_relation.
Require Import isomorphism_theorem.congruence_mapping.
Require Import isomorphism_theorem.image.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Section FirstIsomorphismTheorem.
  Context {Σ : hit_signature}
          {X Y : hit_algebra_one_types Σ}
          (f : X --> Y).

  (**
     Step 1: we define a congruence relation on `X`
     We identitify `x` and `y` if `f x = f y`.
   *)
  Definition congruence_relation_groupoid_for_image
    : congruence_relation_groupoid X.
  Proof.
    use make_congruence_relation_groupoid.
    - exact (λ x y, alg_map_carrier f x = alg_map_carrier f y).
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
  Defined.

  Definition congruence_relation_ops_for_image
    : congruence_relation_ops X.
  Proof.
    use make_congruence_relation_ops.
    - exact congruence_relation_groupoid_for_image.
    - apply TODO.
    - apply TODO.
    - apply TODO.
  Defined.
  
  Definition congruence_relation_nat_for_image
    : congruence_relation_nat X.
  Proof.
    use make_congruence_relation_nat.
    - exact congruence_relation_ops_for_image.
    - apply TODO.
  Defined.
  
  Definition congruence_relation_for_image
    : congruence_relation X.
  Proof.
    use make_congruence_relation.
    - exact congruence_relation_nat_for_image.
    - apply TODO.
  Defined.

  (** Notation for the quotient *)
  Local Notation "'X/R'" := (quotient_of_congruence congruence_relation_for_image).
  
  (**
     Step 2: Define a map from the quotient to `im f`.
   *)
  Definition map_gquot_to_image
    : X/R --> image f.
  Proof.
    use factor_through_gquot.
    - exact (image_inj f).
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
  Defined.

  (**
     Step 3: Show this map is a left adjoint equivalence
   *)
  Definition map_gquot_to_image_is_adjequiv
    : left_adjoint_equivalence map_gquot_to_image.
  Proof.
    use isweq_to_hit_algebra_adjequiv.
    intro y.
    induction y as [y p].
    simpl in p.
    revert p.
    use (squash_rec
           (λ p, make_hProp
                   (iscontr (hfiber (alg_map_carrier map_gquot_to_image) (y,, p)))
                   _)).
    - apply isapropiscontr.
    - intro x ; simpl.
      induction x as [x p].
      induction p ; simpl.
      use make_iscontr.
      + exact (gcl (make_groupoid_algebra_carrier _) x ,, idpath _).
      + intro t.
        induction t as [z p].
        apply TODO.
  Defined.
End FirstIsomorphismTheorem.
