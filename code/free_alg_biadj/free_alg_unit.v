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

Local Open Scope cat.

Opaque hit_existence.
Opaque make_free_alg_algebra.
Opaque free_ump_1.
Opaque free_alg_ump_2.
Opaque free_alg_ump_eq.

Arguments free_alg_mor_on_A {_ _ _} _ _.

Section FreeAlgebraUnit.
  Variable (Σ : hit_signature).
  
  Definition free_alg_unit_comp
             (X : one_type)
    : X → alg_carrier (free_alg_psfunctor_obj Σ X)
    := λ x, alg_constr (free_alg Σ X) (inr x).

  Definition free_alg_unit_natural
             {X Y : one_type}
             (f : X → Y)
             (x : X)
    : alg_map_carrier (free_alg_psfunctor_mor Σ f) (free_alg_unit_comp X x)
      =
      free_alg_unit_comp Y (f x)
    := free_alg_mor_on_A f x.

  Definition free_alg_unit_data
    : pstrans_data
        (id_psfunctor one_types)
        (comp_psfunctor
           (hit_algebra_underlying Σ)
           (free_alg_psfunctor Σ)).
  Proof.
    use make_pstrans_data.
    - exact free_alg_unit_comp.
    - intros X Y f.
      use make_invertible_2cell.
      + exact (free_alg_unit_natural f).
      + apply one_type_2cell_iso.
  Defined.

  Local Definition free_alg_unit_natural_natural
        {X Y : one_type}
        {f g : X → Y}
        (p : f ~ g)
        (x : X)
    : alg_2cell_carrier
        (free_alg_psfunctor_cell Σ p)
        (free_alg_unit_comp X x)
      @ free_alg_unit_natural g x
      =
      free_alg_unit_natural f x
      @ maponpaths (free_alg_unit_comp Y) (p x).
  Proof.
    apply free_alg_psfunctor_cell_on_A.
  Qed.

  Local Definition free_alg_unit_id
        (X : one_type)
        (x : X)
    : alg_2cell_carrier (free_alg_psfunctor_id _ X) (free_alg_unit_comp X x)
      @ free_alg_unit_natural (λ x0 : X, x0) x
      =
      idpath _.
  Proof.
    etrans.
    {
      apply maponpaths_2.
      apply free_alg_psfunctor_id_on_A.
    }
    apply pathsinv0l.
  Qed.

  Local Definition free_alg_unit_composition
             {X Y Z : one_type}
             (f : X → Y) (g : Y → Z)
             (x : X)
    : alg_2cell_carrier (free_alg_psfunctor_comp Σ f g) (free_alg_unit_comp X x)
      @ free_alg_unit_natural (λ z, g (f z)) x
      =
      (((maponpaths (alg_map_carrier (free_alg_psfunctor_mor Σ g)) (free_alg_unit_natural f x)
         @ idpath _)
        @ free_alg_unit_natural g (f x))
       @ idpath _)
      @ idpath _.
  Proof.
    refine (!_).
    do 2 refine (pathscomp0rid _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply pathscomp0rid.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (free_alg_psfunctor_comp_on_A Σ f g x).
    }
    refine (!(path_assoc _ _ _) @ _) ; apply maponpaths.
    refine (_ @ pathscomp0rid _).
    refine (!(path_assoc _ _ _) @ _) ; apply maponpaths.
    apply pathsinv0l.
  Qed.

  Definition free_alg_unit_is_pstrans
    : is_pstrans free_alg_unit_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      exact (free_alg_unit_natural_natural p).
    - intro X.
      use funextsec.
      exact (free_alg_unit_id X).
    - intros X Y Z f g.
      use funextsec.
      exact (free_alg_unit_composition f g).
  Qed.

  Definition free_alg_unit
    : pstrans
        (id_psfunctor one_types)
        (comp_psfunctor
           (hit_algebra_underlying Σ)
           (free_alg_psfunctor Σ)).
  Proof.
    use make_pstrans.
    - exact free_alg_unit_data.
    - exact free_alg_unit_is_pstrans.
  Defined.
End FreeAlgebraUnit.
