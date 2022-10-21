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

Local Open Scope cat.

Opaque hit_existence.
Opaque make_free_alg_algebra.
Opaque free_ump_1.
Opaque free_alg_ump_2.
Opaque free_alg_ump_eq.
Opaque comp_psfunctor.

Section FreeAlgebraCounit.
  Variable (Σ : hit_signature).

  Definition free_alg_counit_comp
             (X : hit_algebra_one_types Σ)
    : free_alg_psfunctor_obj _ (pr111 X) --> X.
  Proof.
    use free_ump_1.
    - apply free_alg_is_initial.
    - exact (λ z, z).
  Defined.
  
  Definition free_alg_counit_comp_on_A
             (X : hit_algebra_one_types Σ)
             (x : alg_carrier X)
    : alg_map_carrier (free_alg_counit_comp X) (free_alg_inc _ x)
      =
      x
    := free_alg_one_cell_on_A _ X (λ z, z) x.

  Definition free_alg_counit_natural
             {X Y : hit_algebra_one_types Σ}
             (f : X --> Y)
    : free_alg_counit_comp X · f
      ==>
      free_alg_psfunctor_mor Σ (alg_map_carrier f)
      · free_alg_counit_comp Y.
  Proof.
    use free_alg_ump_2.
    - apply free_alg_is_initial.
    - exact (alg_map_carrier f).
    - intro x.
      exact (maponpaths (alg_map_carrier f) (free_alg_one_cell_on_A _ _ _ _)).
    - exact (λ x,
             maponpaths
               (alg_map_carrier (free_alg_counit_comp Y))
               (free_alg_mor_on_A (alg_map_carrier f) x)
             @ free_alg_counit_comp_on_A Y (alg_map_carrier f x)).
  Defined.

  
  Definition free_alg_counit_natural_on_A_type
             {X Y : hit_algebra_one_types Σ}
             (f : X --> Y)
             (x : alg_carrier X)
    : UU.
  Proof.
    exact
      (alg_2cell_carrier (free_alg_counit_natural f) (free_alg_inc _ x)
       @ maponpaths
           (alg_map_carrier (free_alg_counit_comp Y))
           (free_alg_mor_on_A (alg_map_carrier f) _)
       @ free_alg_counit_comp_on_A Y (alg_map_carrier f x)
       =
       maponpaths (alg_map_carrier f) (free_alg_one_cell_on_A _ _ _ x)).
  Defined.

  Definition free_alg_counit_natural_on_A
             {X Y : hit_algebra_one_types Σ}
             (f : X --> Y)
             (x : alg_carrier X)
    : free_alg_counit_natural_on_A_type f x.
  Proof.
    exact (free_alg_ump_2_on_A _ _ _ _ _ x).
  Qed.

  Definition free_alg_counit_data
    : pstrans_data
        (comp_psfunctor (free_alg_psfunctor Σ) (hit_algebra_underlying Σ))
        (id_psfunctor (hit_algebra_one_types Σ)).
  Proof.
    use make_pstrans_data.
    - exact free_alg_counit_comp.
    - intros X Y f.
      use make_invertible_2cell.
      + exact (free_alg_counit_natural f).
      + apply hit_alg_is_invertible_2cell_one_type.
  Defined.

  Opaque identity compose.

  Definition free_alg_counit_is_pstrans
    : is_pstrans free_alg_counit_data.
  Proof.
    repeat split.
    - intros X Y f g τ.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, alg_map_carrier g x).
      + exact (λ x, maponpaths (alg_map_carrier f) (free_alg_counit_comp_on_A X x)
                    @ alg_2cell_carrier τ x).
      + exact (λ x,
               maponpaths
                 (alg_map_carrier (free_alg_counit_comp Y))
                 (free_alg_mor_on_A (alg_map_carrier g) x)
               @ free_alg_counit_comp_on_A Y (alg_map_carrier g x)).
      + intro x ; cbn ; unfold homotcomp, funhomotsec.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (free_alg_counit_natural_on_A g x).
        }
        refine (!_).
        exact (homotsec_natural'
                 (alg_2cell_carrier τ)
                 (free_alg_counit_comp_on_A X x)).
      + intro x.
        assert (alg_2cell_carrier
                  (free_alg_counit_natural f)
                  (free_alg_inc _ x)
                @ maponpaths
                    (alg_map_carrier (free_alg_counit_comp Y))
                    (alg_2cell_carrier
                       (free_alg_psfunctor_cell _ (alg_2cell_carrier τ))
                       (free_alg_inc _ x))
                @ maponpaths
                    (alg_map_carrier (free_alg_counit_comp Y))
                    (free_alg_mor_on_A (alg_map_carrier g) x)
                @ free_alg_counit_comp_on_A Y (alg_map_carrier g x)
                =
                maponpaths
                  (alg_map_carrier f)
                  (free_alg_counit_comp_on_A X x)
                @ alg_2cell_carrier τ x)
          as H.
        {
          etrans.
          {
            apply maponpaths.
            refine (path_assoc _ _ _ @ _).
            apply maponpaths_2.
            etrans.
            {
              refine (!_).
              apply (maponpathscomp0
                       (alg_map_carrier (free_alg_counit_comp Y))
                       (alg_2cell_carrier
                          (free_alg_psfunctor_cell Σ (alg_2cell_carrier τ))
                          (free_alg_inc (free_alg Σ (path_alg_carrier (pr1 X))) x))).
            }
            etrans.
            {
              apply maponpaths.
              exact (free_alg_psfunctor_cell_on_A Σ (alg_2cell_carrier τ) x).
            }
            apply (maponpathscomp0
                     (alg_map_carrier (free_alg_counit_comp Y))
                     (free_alg_mor_on_A (alg_map_carrier f) x)).
          }
          etrans.
          {
            apply maponpaths.
            refine (!(path_assoc _ _ _) @ _).
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              apply maponpathscomp.
            }
            etrans.
            {
              apply (homotsec_natural' (free_alg_counit_comp_on_A Y)).
            }
            apply maponpaths.
            apply maponpathsidfun.
          }
          do 2 refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(path_assoc _ _ _) @ _).
          exact (free_alg_counit_natural_on_A f x).
        }
        refine (!(path_assoc _ _ _) @ _).
        exact H.
    - intros X.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, x).
      + exact (free_alg_counit_comp_on_A X).
      + intro x.
        refine (_ @ free_alg_counit_comp_on_A X x).
        refine (maponpaths (alg_map_carrier (free_alg_counit_comp X)) _).
        exact (@free_alg_mor_on_A Σ (pr111 X) (pr111 X) (λ z, z) x).
      + intro x ; cbn.
        refine (_ @ free_alg_counit_natural_on_A (id₁ X) x @ maponpathsidfun _).
        apply idpath.
      + intro x ; cbn ; unfold homotfun.
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (maponpathscomp0 (alg_map_carrier (free_alg_counit_comp X))).
        }
        refine (_ @ pathscomp0lid _).
        apply maponpaths_2.
        refine (_ @ @maponpaths_idpath _ _ (alg_map_carrier (free_alg_counit_comp X)) _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          exact (alg_2cell_eq_component
                   (comp_psfunctor_psfunctor_id
                      (free_alg_psfunctor Σ)
                      (hit_algebra_underlying Σ)
                      X)
                   (free_alg_inc _ x)).
        }
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (@free_alg_psfunctor_cell_on_A
                   Σ
                   (pr111 X) (pr111 X)
                   (λ z, z) (λ z, z)
                   (homotrefl _) x).
        }
        refine (path_assoc _ _ _ @ _).
        refine (pathscomp0rid _ @ _).
        etrans.
        {
          apply maponpaths_2.
          exact (free_alg_psfunctor_id_on_A Σ (pr111 X) x).
        }
        apply pathsinv0l.
    - intros X Y Z f g.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ z, alg_map_carrier g (alg_map_carrier f z)).
      + intro x.
        exact (maponpaths
                 (λ z, alg_map_carrier g (alg_map_carrier f z))
                 (free_alg_counit_comp_on_A X x)).
      + intro x.
        exact (maponpaths
                 (alg_map_carrier (free_alg_counit_comp Z))
                 (free_alg_mor_on_A _ _)
               @ free_alg_counit_comp_on_A _ _).
      + intro x ; cbn.
        refine (_ @ free_alg_counit_natural_on_A (f · g) x)
        ; apply idpath.
      + intro x ; cbn ; unfold homotcomp, homotfun, funhomotsec ; cbn.
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply pathscomp0rid.
          }
          refine (maponpaths (λ z, z @ _) _).
          apply pathscomp0rid.
        }
        assert
          (((maponpaths
               (alg_map_carrier g)
               (alg_2cell_carrier (free_alg_counit_natural f) (free_alg_inc _ x))
             @ alg_2cell_carrier
                 (free_alg_counit_natural g)
                 _)
            @ maponpaths
                (alg_map_carrier (free_alg_counit_comp Z))
                (alg_2cell_carrier
                   (free_alg_psfunctor_comp
                      _
                      (alg_map_carrier f)
                      (alg_map_carrier g))
                   (free_alg_inc _ x)))
           @ maponpaths
               (alg_map_carrier (free_alg_counit_comp Z))
               (free_alg_mor_on_A (alg_map_carrier (f · g)) x)
           @ free_alg_counit_comp_on_A Z (alg_map_carrier (f · g) x)    
           =
           maponpaths
             (λ z, alg_map_carrier g (alg_map_carrier f z))
             (free_alg_counit_comp_on_A X x))
          as H.
        {
          do 2 refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            do 2 apply maponpaths.
            refine (path_assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (!_).
            apply (maponpathscomp0
                     (alg_map_carrier (free_alg_counit_comp Z))
                     (alg_2cell_carrier
                        (free_alg_psfunctor_comp
                           Σ
                           (alg_map_carrier f)
                           (alg_map_carrier g))
                        (free_alg_inc (free_alg Σ (path_alg_carrier (pr1 X))) x))).
          }
          etrans.
          {
            do 2 apply maponpaths.
            apply maponpaths_2.
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              exact (free_alg_psfunctor_comp_on_A
                       _
                       (alg_map_carrier f) (alg_map_carrier g)
                       x).
            }
            refine (!(path_assoc _ _ _) @ _).
            apply maponpaths.
            refine (!(path_assoc _ _ _) @ _).
            etrans.
            {
              apply maponpaths.
              apply pathsinv0l.
            }
            apply pathscomp0rid.
          }
          etrans.
          {
            do 2 apply maponpaths.
            apply maponpaths_2.
            etrans.
            {
              apply (maponpathscomp0
                       (alg_map_carrier (free_alg_counit_comp Z))
                       (maponpaths
                          (alg_map_carrier (free_alg_psfunctor_mor Σ (alg_map_carrier g)))
                          (free_alg_mor_on_A (alg_map_carrier f) x))).
            }
            apply maponpaths_2.
            apply maponpathscomp.
          }
          etrans.
          {
            apply maponpaths.
            refine (path_assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (path_assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (!_).
            exact (homotsec_natural'
                     (alg_2cell_carrier (free_alg_counit_natural g))
                     (free_alg_mor_on_A (alg_map_carrier f) x)).
          }
          etrans.
          {
            apply maponpaths.
            do 2 refine (!(path_assoc _ _ _) @ _).
            apply maponpaths.
            exact (free_alg_counit_natural_on_A g _).
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              exact (!(maponpathscomp
                         (alg_map_carrier (free_alg_counit_comp Y))
                         (alg_map_carrier g)
                         _)).
            }
            refine (!_).
            exact (maponpathscomp0
                     (alg_map_carrier g)
                     (maponpaths
                        (alg_map_carrier (free_alg_counit_comp Y))
                        (free_alg_mor_on_A (alg_map_carrier f) x))
                     (free_alg_one_cell_on_A
                        (free_alg_is_initial Σ (pr111 Y)) Y (λ z, z)
                        (alg_map_carrier f x))).
          }
          etrans.
          {
            refine (!_).
            exact (maponpathscomp0
                     (alg_map_carrier g)
                     (alg_2cell_carrier
                        (free_alg_counit_natural f)
                        (free_alg_inc (free_alg Σ (pr111 X)) x))
                     (maponpaths
                        (alg_map_carrier (free_alg_counit_comp Y))
                        (free_alg_mor_on_A (alg_map_carrier f) x)
                      @ free_alg_one_cell_on_A
                          (free_alg_is_initial Σ (pr111 Y))
                          Y (λ z, z)
                          (alg_map_carrier f x))).
          }
          etrans.
          {
            apply maponpaths.
            exact (free_alg_counit_natural_on_A f x).
          }
          exact (maponpathscomp
                   (alg_map_carrier f)
                   (alg_map_carrier g)
                   (free_alg_counit_comp_on_A X x)).
        }
        refine (_ @ H) ; clear H.
        refine (maponpaths (λ z, z @ _) _).
        refine (maponpaths
                  (λ z, (maponpaths
                           (alg_map_carrier g)
                           (alg_2cell_carrier
                              (free_alg_counit_natural f)
                              (free_alg_inc (free_alg Σ (pr111 X)) x))
                         @ alg_2cell_carrier
                             (free_alg_counit_natural g)
                             (alg_map_carrier
                                (free_alg_psfunctor_mor Σ (alg_map_carrier f))
                                (free_alg_inc (free_alg Σ (pr111 X)) x)))
                        @ z)
                  _).
        refine (maponpaths
                  (maponpaths (alg_map_carrier (free_alg_counit_comp Z)))
                  _).
        etrans.
        {
          exact (alg_2cell_eq_component
                   (comp_psfunctor_psfunctor_comp
                      (free_alg_psfunctor Σ)
                      (hit_algebra_underlying Σ)
                      f g)
                   (free_alg_inc _ x)).
        }
        cbn ; unfold homotcomp, homotrefl.
        refine (_ @ pathscomp0rid _).
        apply maponpaths.
        refine (!(pathscomp0rid _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (!(pathsinv0r
                     (free_alg_mor_on_A
                        (λ z, alg_map_carrier g (alg_map_carrier f z))
                        x))).
        }
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            exact (free_alg_psfunctor_cell_on_A
                     Σ
                     (homotrefl (λ z, alg_map_carrier g (alg_map_carrier f z)))
                     x).
          }
          apply pathscomp0rid.
        }
        apply pathsinv0r.
  Qed.
  
  Definition free_alg_counit
    : pstrans
        (comp_psfunctor (free_alg_psfunctor Σ) (hit_algebra_underlying Σ))
        (id_psfunctor (hit_algebra_one_types Σ)).
  Proof.
    use make_pstrans.
    - exact free_alg_counit_data.
    - exact free_alg_counit_is_pstrans.
  Defined.
End FreeAlgebraCounit.  
