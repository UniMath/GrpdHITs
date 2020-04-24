(** Congruence relation of algebras *)
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
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.
Require Import hit_biadjunction.gquot_commute.
Require Import hit_biadjunction.gquot_natural.
Require Import hit_biadjunction.hit_algebra_biadj.lift_gquot.
Require Import hit_biadjunction.hit_path_algebra_biadj.lift_gquot.
Require Import hit_biadjunction.hit_path_algebra_biadj.counit.
Require Import hit_biadjunction.hit_path_algebra_biadj.unit.
Require Import hit_biadjunction.hit_algebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_algebra_biadj.
Require Import existence.initial_algebra.
Require Import isomorphism_theorem.congruence_relation.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

(** Mapping principle for the quotient *)
Section MapToQuotientFromCongruence.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}
          (R : congruence_relation X)
          (Y : hit_algebra_one_types Σ).

  Definition quotient_of_congruence_map
             (F : make_groupoid_algebra R
                  -->
                  hit_algebra_biadjunction Σ Y)
    : quotient_of_congruence R --> Y
    := biadj_left_hom
         (hit_algebra_biadjunction Σ)
         (make_groupoid_algebra R)
         Y
         F.

  Variable (f : alg_carrier X → alg_carrier Y)
           (fR : ∏ (a b : alg_carrier X),
                 cong_rel_carrier R a b → f a = f b).

  Definition test_prealg_carrier_data
    : functor_data
        (alg_carrier_grpd (make_groupoid_algebra R))
        (alg_carrier_grpd (hit_algebra_biadjunction Σ Y)).
  Proof.
    use make_functor_data.
    - exact f.
    - exact fR.
  Defined.

  Definition test_prealg_carrier_is_functor
    : is_functor test_prealg_carrier_data.
  Proof.
    apply TODO.
  Qed.
  
  Definition test_prealg_carrier
    : alg_carrier_grpd (make_groupoid_algebra R)
                       ⟶
                       alg_carrier_grpd (hit_algebra_biadjunction Σ Y).
  Proof.
    use make_functor.
    - exact test_prealg_carrier_data.
    - exact test_prealg_carrier_is_functor.
  Defined.

  Definition test_prealg
    : pr11 (make_groupoid_algebra R) --> pr11 (hit_algebra_biadjunction Σ Y).
  Proof.
    use make_hit_prealgebra_mor.
    - exact test_prealg_carrier.
    - apply TODO.
  Defined.

  Definition test
    : make_groupoid_algebra R
                            -->
                            hit_algebra_biadjunction Σ Y.
  Proof.
    use make_algebra_map_grpd.
    use make_hit_path_alg_map_grpd.
    - exact test_prealg.
    - apply TODO.
  Defined.

  Definition test_map
    : quotient_of_congruence R --> Y.
  Proof.
    use quotient_of_congruence_map.
    exact test.
  Defined.
End MapToQuotientFromCongruence.
