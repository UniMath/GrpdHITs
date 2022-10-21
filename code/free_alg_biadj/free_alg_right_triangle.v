Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.
Require Import examples.free_algebra.
Require Import free_alg_biadj.free_alg_functor.
Require Import free_alg_biadj.free_alg_unit.
Require Import free_alg_biadj.free_alg_counit.
Require Import free_alg_biadj.free_alg_biadjunction_unit_counit.

Local Open Scope cat.

Opaque hit_existence.
Opaque make_free_alg_algebra.
Opaque free_ump_1.
Opaque free_alg_ump_2.
Opaque free_alg_ump_eq.

Section FreeAlgebraRightTriangle.
  Variable (Σ : hit_signature).
    
  Definition free_alg_right_triangle_data
    : invertible_modification_data
        (biadj_triangle_r_lhs (free_alg_unit_counit Σ))
        (id_pstrans (free_alg_unit_counit Σ)).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (free_alg_counit_comp_on_A Σ X).
    - apply one_type_2cell_iso.
  Defined.

  Local Lemma free_alg_right_is_modification_help
        {X Y : hit_algebra_one_types Σ}
        (f : hit_algebra_one_types Σ ⟦ X, Y ⟧)
        (x : alg_carrier X)
    : ((((((((((maponpaths
                  (λ x0, x0)
                  (alg_2cell_carrier
                     (free_alg_counit_natural Σ f)
                     (free_alg_unit_comp Σ (pr111 X) x)
                     @ idpath _)
                  @ idpath _)
                 @ idpath _)
                @ idpath _)
               @ idpath _)
              @ idpath _)
             @ maponpaths
                 (λ (z : alg_carrier (free_alg Σ (pr111 Y))),
                  alg_map_carrier (free_alg_counit_comp Σ Y) z)
                 (free_alg_unit_natural Σ (alg_map_carrier f) x))
            @ idpath _)
           @ idpath _)
          @ idpath _)
         @ idpath _)
        @ free_alg_counit_comp_on_A Σ Y (alg_map_carrier f x)
      =
      maponpaths
        (alg_map_carrier f)
        (free_alg_counit_comp_on_A Σ X x)
      @ idpath _.
  Proof.
    etrans.
    {
      apply maponpaths_2.
      do 4 refine (pathscomp0rid _ @ _).
      apply maponpaths_2.
      do 5 refine (pathscomp0rid _ @ _).
      apply maponpaths.
      apply pathscomp0rid.
    }
    refine (_ @ !(pathscomp0rid _)).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpathsidfun.
    }
    refine (!(path_assoc _ _ _) @ _).
    exact (free_alg_counit_natural_on_A Σ f x).
  Qed.

  Opaque compose.

  Definition free_alg_right_is_modification
    : is_modification free_alg_right_triangle_data.
  Proof.
    intros X Y f.
    use funextsec.
    exact (free_alg_right_is_modification_help f).
  Qed.

  Definition free_alg_right_triangle
    : biadj_triangle_r_law (free_alg_unit_counit Σ).
  Proof.
    use make_invertible_modification.
    - exact free_alg_right_triangle_data.
    - exact free_alg_right_is_modification.
  Defined.
End FreeAlgebraRightTriangle.

