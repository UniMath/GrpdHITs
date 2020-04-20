Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.
Require Import existence.hit_existence.
Require Import examples.free_algebra.

Definition TODO {A : UU} : A.
Admitted.

Local Open Scope cat.

(**
- set the right implicit arguments
- make the right functions opaque
 *)

Section FreeAlgebraFunctor.
  Variable (Σ : hit_signature).
  
  Local Definition free_alg
        (X : one_type)
    := hit_existence (free_alg_signature Σ X).

  Definition free_alg_psfunctor_obj
    : one_types → hit_algebra_one_types Σ
    := λ X, free_alg_is_alg _ _ (pr1 (free_alg X)).

  Definition free_alg_psfunctor_mor
             {X Y : one_type}
             (f : X → Y)
    : free_alg_psfunctor_obj X --> free_alg_psfunctor_obj Y.
  Proof.
    use free_ump_1.
    - pose (pr2 (free_alg X)). 
      apply TODO.
    - exact (λ x, free_alg_inc Σ Y _ (f x)).
  Defined.

  Definition free_alg_psfunctor_cell
             {X Y : one_type}
             {f g : X → Y}
             (p : f ~ g)
    : free_alg_psfunctor_mor f ==> free_alg_psfunctor_mor g.
  Proof.
    use free_alg_ump_2.
    - apply TODO.
    - exact (λ x, free_alg_inc Σ Y _ (f x)).
    - intro a.
      exact (free_alg_one_cell_on_A
               Σ X
               (pr1 (free_alg X)) _
               (free_alg_is_alg _ _ (pr1 (free_alg Y)))
               _ a).
    - apply TODO.
  Defined.

  Definition free_alg_psfunctor_id
             (X : one_types)
    : id₁ (free_alg_psfunctor_obj X) ==> free_alg_psfunctor_mor (id₁ X).
  Proof.
    use free_alg_ump_2.
    - apply TODO.
    - exact (free_alg_inc Σ X _).
    - exact (λ a, idpath _).
    - apply TODO.
  Defined.

  Definition free_alg_psfunctor_comp
             {X Y Z : one_type}
             (f : X → Y)
             (g : Y → Z)
    : free_alg_psfunctor_mor f · free_alg_psfunctor_mor g
      ==>
      free_alg_psfunctor_mor (λ z, g(f z)).
  Proof.
    use free_alg_ump_2.
    - apply TODO.
    - exact (λ x, free_alg_inc Σ Z _ (g(f x))).
    - apply TODO.
    - apply TODO.
  Defined.

  Definition free_alg_psfunctor_data
    : psfunctor_data one_types (hit_algebra_one_types Σ).
  Proof.
    use make_psfunctor_data.
    - exact free_alg_psfunctor_obj.
    - exact @free_alg_psfunctor_mor.
    - exact @free_alg_psfunctor_cell.
    - exact @free_alg_psfunctor_id.
    - exact @free_alg_psfunctor_comp.
  Defined.

  Definition free_alg_psfunctor_laws
    : psfunctor_laws free_alg_psfunctor_data.
  Proof.
    refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - intros X Y f.
      use free_alg_ump_eq.
      + apply TODO.
      + exact (λ x, free_alg_inc Σ Y _ (f x)).
      + intro a.
        apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
  Qed.

  Definition free_alg_psfunctor_invertible_cells
    : invertible_cells free_alg_psfunctor_data.
  Proof.
    split ; intros ; apply hit_alg_is_invertible_2cell_one_type.
  Defined.
  
  Definition free_alg_psfunctor
    : psfunctor one_types (hit_algebra_one_types Σ).
  Proof.
    use make_psfunctor.
    - exact free_alg_psfunctor_data.
    - exact free_alg_psfunctor_laws.
    - exact free_alg_psfunctor_invertible_cells.
  Defined.
End FreeAlgebraFunctor.
