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

Section FreeAlgebraLeftTriangle.
  Variable (Σ : hit_signature).
  
  Definition free_alg_left_triangle_comp
             (X : one_type)
    : biadj_triangle_l_lhs (free_alg_unit_counit Σ) X
      ==>
      id_pstrans (free_alg_psfunctor Σ) X.
  Proof.
    use free_alg_ump_2.
    - apply free_alg_is_initial.
    - exact (free_alg_inc (free_alg _ X)).
    - intro x.
      exact (maponpaths
               (alg_map_carrier (free_alg_counit_comp _ _))
               (free_alg_mor_on_A (free_alg_unit_comp Σ X) x)
             @ free_alg_counit_comp_on_A Σ (free_alg_psfunctor_obj Σ X) _).
    - exact (λ _, idpath _).
  Defined.

  Definition free_alg_left_triangle_comp_on_A
             (X : one_type)
             (x : X)
    : alg_2cell_carrier
        (free_alg_left_triangle_comp X)
        (free_alg_inc _ x)
      =
      maponpaths
        (alg_map_carrier (free_alg_counit_comp _ _))
        (free_alg_mor_on_A (free_alg_unit_comp Σ X) x)
      @ free_alg_counit_comp_on_A Σ (free_alg_psfunctor_obj Σ X) _.
  Proof.
    refine (!(pathscomp0rid _) @ _).
    exact (free_alg_ump_2_on_A _ _ _ _ _ x).
  Qed.
  
  Definition free_alg_left_triangle_data
    : invertible_modification_data
        (biadj_triangle_l_lhs (free_alg_unit_counit Σ))
        (id_pstrans (free_alg_psfunctor Σ)).
  Proof.
    intro X.
    use make_invertible_2cell.
    - exact (free_alg_left_triangle_comp X).
    - apply hit_alg_is_invertible_2cell_one_type.
  Defined.

  Definition free_alg_counit_natural_on_A_help
             {X Y : one_type}
             (f : X → Y)
             (x : X)
    : alg_2cell_carrier
        (free_alg_counit_natural Σ (free_alg_psfunctor_mor Σ f))
        (free_alg_inc _ (free_alg_unit_comp Σ X x))
      @ maponpaths
          (alg_map_carrier (free_alg_counit_comp Σ (free_alg_psfunctor_obj Σ Y)))
          (free_alg_mor_on_A
             (alg_map_carrier (free_alg_psfunctor_mor Σ f))
             (free_alg_unit_comp Σ X x))
      @ free_alg_counit_comp_on_A
          Σ (free_alg_psfunctor_obj Σ Y)
          (alg_map_carrier
             (free_alg_psfunctor_mor Σ f)
             (free_alg_unit_comp Σ X x))
      =
      maponpaths
        (alg_map_carrier (free_alg_psfunctor_mor Σ f))
        (free_alg_counit_comp_on_A
           Σ
           (free_alg_psfunctor_obj Σ X)
           (free_alg_unit_comp Σ X x)).
  Proof.
    exact (free_alg_counit_natural_on_A
             Σ
             (free_alg_psfunctor_mor Σ f)
             (free_alg_unit_comp Σ X x)).
  Qed.
  
  Local Lemma free_alg_left_triangle_is_modification_help
        {X Y : one_type}
        (f : X → Y)
        (x : X)
    : (((((((((((maponpaths
                   (λ (z : alg_carrier (free_alg Σ Y)), z)
                   (alg_2cell_carrier
                      (free_alg_counit_natural Σ (free_alg_psfunctor_mor Σ f))
                      (alg_map_carrier
                         (free_alg_psfunctor_mor Σ (free_alg_unit_comp Σ X))
                         (free_alg_inc _ x)))
                   @ idpath _)
                  @ idpath _)
                 @ idpath _)
                @ idpath _)
               @ idpath _)
              @ maponpaths
                  (alg_map_carrier (free_alg_counit_comp Σ (free_alg_psfunctor_obj Σ Y)))
                  (((pr111 (free_alg_psfunctor_comp
                              Σ (free_alg_unit_comp Σ X)
                              (alg_map_carrier (free_alg_psfunctor_mor Σ f))))
                              (free_alg_inc (free_alg Σ X) x)
                      @ alg_2cell_carrier
                          (free_alg_psfunctor_cell Σ (free_alg_unit_natural Σ f))
                          (free_alg_inc _ x))
                     @ !(alg_2cell_carrier
                           (free_alg_psfunctor_comp Σ f (free_alg_unit_comp Σ Y))
                           (free_alg_inc _ x))))
             @ idpath _)
            @ idpath _)
           @ idpath _)
          @ idpath _)
         @ alg_2cell_carrier
             (free_alg_left_triangle_comp Y)
             (alg_map_carrier
                (free_alg_psfunctor_mor Σ f)
                (free_alg_inc _ x)))
        @ free_alg_mor_on_A f x
      =
      maponpaths
        (alg_map_carrier (free_alg_psfunctor_mor Σ f))
        (maponpaths
           (alg_map_carrier (free_alg_counit_comp Σ (free_alg_psfunctor_obj Σ X)))
           (free_alg_mor_on_A (free_alg_unit_comp Σ X) x)
      @ free_alg_counit_comp_on_A
          Σ (free_alg_psfunctor_obj Σ X)
          (free_alg_unit_comp Σ X x))
      @ free_alg_mor_on_A f x.
  Proof.
    etrans.
    {
      do 2 apply maponpaths_2.
      do 4 refine (pathscomp0rid _ @ _).
      apply maponpaths_2.
      do 5 refine (pathscomp0rid _ @ _).
      apply maponpathsidfun.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (free_alg_psfunctor_comp_on_A _ f (free_alg_unit_comp Σ Y) x).
        }
        refine (pathscomp_inv _ _ @ _).
        apply maponpaths_2.
        refine (pathscomp_inv _ _ @ _).
        apply maponpaths_2.
        apply pathsinv0inv0.
      }
      etrans.
      {
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        exact (free_alg_psfunctor_cell_on_A Σ (free_alg_unit_natural Σ f) x).
      }
      etrans.
      {
        apply maponpaths_2.
        exact (free_alg_psfunctor_comp_on_A
                 _
                 (free_alg_unit_comp Σ X)
                 (alg_map_carrier (free_alg_psfunctor_mor Σ f))
                 x).
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply pathsinv0l.
      }
      apply pathscomp0lid.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply (maponpathscomp0
                 (alg_map_carrier (free_alg_counit_comp Σ (free_alg_psfunctor_obj Σ Y)))).
      }
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply (maponpathscomp
                 (alg_map_carrier
                    (free_alg_psfunctor_mor
                       Σ
                       (alg_map_carrier (free_alg_psfunctor_mor Σ f))))
                 (alg_map_carrier
                    (free_alg_counit_comp Σ (free_alg_psfunctor_obj Σ Y)))).
      }
      exact (!(homotsec_natural'
                 (alg_2cell_carrier
                    (free_alg_counit_natural Σ (free_alg_psfunctor_mor Σ f)))
                 (free_alg_mor_on_A (free_alg_unit_comp Σ X) x))).
    }
    do 3 refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths_2.
      apply (maponpathscomp
               (alg_map_carrier (free_alg_counit_comp Σ (free_alg_psfunctor_obj Σ X)))
               (alg_map_carrier (free_alg_psfunctor_mor Σ f))).
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp0.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (maponpathsinv0
                   (alg_map_carrier
                      (free_alg_psfunctor_mor Σ (free_alg_unit_comp Σ Y)))).
        }
        apply (maponpathscomp
                 (alg_map_carrier (free_alg_psfunctor_mor Σ (free_alg_unit_comp Σ Y)))
                 (alg_map_carrier (free_alg_counit_comp Σ (free_alg_psfunctor_obj Σ Y)))).
      }
      exact (homotsec_natural'
               (alg_2cell_carrier (free_alg_left_triangle_comp Y))
               (!(free_alg_mor_on_A f x))).
    }  
    do 2 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (free_alg_left_triangle_comp_on_A Y (f x)).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply maponpathscomp0.
      }
      apply maponpaths.
      etrans.
      {
        do 2 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
        apply pathsinv0l.
      }
      apply maponpaths.
      apply pathscomp0rid.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp0.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp.
      }
      exact (homotsec_natural'
               (free_alg_counit_comp_on_A Σ (free_alg_psfunctor_obj Σ Y))
               (free_alg_unit_natural Σ f x)).
    }
    etrans.
    {
      apply maponpaths_2.
      do 3 apply maponpaths.
      apply maponpathsidfun.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpathsidfun.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
    }
    exact (free_alg_counit_natural_on_A_help f x).
  Qed.

  Definition free_alg_left_triangle_is_modification
    : is_modification free_alg_left_triangle_data.
  Proof.
    intros X Y f.
    use free_alg_ump_eq.
    - apply free_alg_is_initial.
    - exact (λ z, free_alg_inc (free_alg _ Y) (f z)). 
    - intro x ; cbn.
      exact (maponpaths
               (alg_map_carrier (free_alg_psfunctor_mor Σ f))
               (maponpaths
                  (alg_map_carrier (free_alg_counit_comp Σ (free_alg_psfunctor_obj Σ X)))
                  (free_alg_mor_on_A (free_alg_unit_comp _ X) x)
                @ free_alg_counit_comp_on_A
                    _
                    (free_alg_psfunctor_obj Σ X)
                    _)
             @ free_alg_mor_on_A f x).
    - exact (free_alg_mor_on_A f).
    - intro x.
      cbn ; unfold homotcomp, funhomotsec, homotfun.
      rewrite !pathscomp0lid.
      exact (free_alg_left_triangle_is_modification_help f x).
    - intro x.
      cbn ; unfold homotcomp, funhomotsec, homotfun.
      apply maponpaths_2.
      refine (pathscomp0rid _ @ _).
      apply maponpaths.
      exact (free_alg_left_triangle_comp_on_A X x).
  Qed.
  
  Definition free_alg_left_triangle
    : biadj_triangle_l_law (free_alg_unit_counit Σ).
  Proof.
    use make_invertible_modification.
    - exact free_alg_left_triangle_data.
    - exact free_alg_left_triangle_is_modification.
  Defined.
End FreeAlgebraLeftTriangle.
