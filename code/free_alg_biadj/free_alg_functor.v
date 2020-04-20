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

Definition TODO {A : UU} : A.
Admitted.

Local Open Scope cat.

Opaque hit_existence.
Opaque make_free_alg_algebra.
Opaque free_ump_1.
Opaque free_alg_ump_2.
Opaque free_alg_ump_eq.

Arguments free_ump_1 {_ _ _} _ _ _.
Arguments free_alg_ump_2 {_ _ _} _ _ _ _ _ _.
Arguments free_alg_ump_eq {_ _ _} _ _ _ _ _ _ _ _ _ _ _.

Arguments free_alg_is_alg {_ _} _.
Arguments free_alg_inc {_ _} _ _.
Arguments free_alg_one_cell_on_A {_ _ _} _ _ _ _.
Arguments free_alg_ump_2_on_A {_ _ _} _ _ _ {_ _} _ _ _.

(**
- set the right implicit arguments
- make the right functions opaque
 *)

Section FreeAlgebraFunctor.
  Variable (Σ : hit_signature).
  
  Local Definition free_alg
        (X : one_type)
    : hit_algebra_one_types (free_alg_signature Σ X)
    := pr1 (hit_existence (free_alg_signature Σ X)).

  Local Definition free_alg_is_initial
        (X : one_type)
    : is_initial _ (free_alg X).
  Proof.
    apply initial_algebra.HIT_is_initial.
    exact (pr2 (hit_existence (free_alg_signature Σ X))).
  Qed.

  Definition free_alg_psfunctor_obj
    : one_types → hit_algebra_one_types Σ
    := λ X, free_alg_is_alg (free_alg X).

  Definition free_alg_psfunctor_mor
             {X Y : one_type}
             (f : X → Y)
    : free_alg_psfunctor_obj X --> free_alg_psfunctor_obj Y.
  Proof.
    use free_ump_1.
    - apply free_alg_is_initial.
    - exact (λ x, free_alg_inc _ (f x)).
  Defined.

  Definition free_alg_psfunctor_cell
             {X Y : one_type}
             {f g : X → Y}
             (p : f ~ g)
    : free_alg_psfunctor_mor f ==> free_alg_psfunctor_mor g.
  Proof.
    use free_alg_ump_2.
    - apply free_alg_is_initial.
    - exact (λ x, free_alg_inc _ (g x)).
    - intro x.
      exact (free_alg_one_cell_on_A
               (free_alg_is_initial X)
               (free_alg_psfunctor_obj Y)
               (λ z, free_alg_inc _ (f z))
               x
             @ maponpaths (free_alg_inc (free_alg Y)) (p x)).
    - exact (free_alg_one_cell_on_A
               (free_alg_is_initial X)
               (free_alg_psfunctor_obj Y)
               (λ x, free_alg_inc _ (g x))).
  Defined.

  Definition free_alg_psfunctor_id
             (X : one_types)
    : id₁ (free_alg_psfunctor_obj X) ==> free_alg_psfunctor_mor (id₁ X).
  Proof.
    use free_alg_ump_2.
    - apply free_alg_is_initial.
    - exact (free_alg_inc _).
    - exact (λ x, idpath _).
    - exact (free_alg_one_cell_on_A
               (free_alg_is_initial X)
               (free_alg_psfunctor_obj X)
               (free_alg_inc _)).
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
    - apply free_alg_is_initial.
    - exact (λ x, free_alg_inc _ (g(f x))).
    - intro x.
      refine (_ @ _).
      + refine (maponpaths (alg_map_carrier (free_alg_psfunctor_mor g)) _).
        exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc _ (f z))
                 x).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial Y)
                 (free_alg_psfunctor_obj Z)
                 (λ z, free_alg_inc _ (g z))
                 _).
    - exact (free_alg_one_cell_on_A
               (free_alg_is_initial X)
               (free_alg_psfunctor_obj Z)
               (λ z, free_alg_inc _ (g(f z)))).
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
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (f x)).
      + exact (λ x,
               free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc _ (f z))
                 x
               @ maponpaths (free_alg_inc (free_alg Y)) (idpath _)).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc _ (f z))).
      + intro x ; cbn.
        exact (free_alg_ump_2_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc _ (f z))
                 _
                 _
                 x).
      + intro x ; cbn.
        exact (!(pathscomp0rid _)).
    - intros X Y f g h τ θ.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (f x)).
      + exact (λ x,
               free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc _ (f z))
                 x
                 @ maponpaths (free_alg_inc (free_alg Y)) (idpath _)).
      + apply TODO.
      + apply TODO.
      + apply TODO.
    - intros X Y f.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (f x)).
      + apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
    - intros X Y f.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (f x)).
      + apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
    - intros W X Y Z f g h.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (h(g(f x)))).
      + apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
    - intros X Y Z f g₁ g₂ τ.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
    - intros X Y Z f₁ f₂ g τ.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
      + apply TODO.
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
