(** Commuation of path groupoid with the constant and identity polynomial *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

Opaque comp_psfunctor.

(** Commutation of path groupoid with constant *)
Section PathGroupoidConstant.
  Variable (A : one_types).

  Definition const_path_groupoid_data
    : pstrans_data (comp_psfunctor ⦃ C A ⦄ path_groupoid) (comp_psfunctor path_groupoid (⟦ C A ⟧)).
  Proof.
    use make_pstrans_data.
    - exact (λ _, functor_identity _).
    - intros X Y f.
      use make_invertible_2cell.
      + use make_nat_trans.
        * exact idpath.
        * abstract
            (intros a b p ;
             induction p ;
             exact (idpath (idpath a))).
      + apply grpd_bicat_is_invertible_2cell.
  Defined.

  Definition const_path_groupoid_is_pstrans
    : is_pstrans const_path_groupoid_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      exact (idpath (idpath x)).
    - intros X.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      exact (idpath (idpath x)).
    - intros X Y Z f g.
      use nat_trans_eq.
      { apply homset_property. }
      intro x.
      exact (idpath (idpath x)).
  Qed.

  Definition const_path_groupoid
    : pstrans (comp_psfunctor ⦃ C A ⦄ path_groupoid) (comp_psfunctor path_groupoid (⟦ C A ⟧)).
  Proof.
    use make_pstrans.
    - exact const_path_groupoid_data.
    - exact const_path_groupoid_is_pstrans.
  Defined.
End PathGroupoidConstant.

(** Commutation of path groupoid with identity *)
Definition id_path_groupoid_data
  : pstrans_data (comp_psfunctor ⦃ I ⦄ path_groupoid) (comp_psfunctor path_groupoid (⟦ I ⟧)).
Proof.
  use make_pstrans_data.
  - exact (λ _, functor_identity _).
  - intros X Y f.
    use make_invertible_2cell.
    + use make_nat_trans.
      * exact (λ _, idpath _).
      * abstract
          (intros a b p ;
           induction p ;
           apply idpath).
    + apply grpd_bicat_is_invertible_2cell.
Defined.

Definition id_path_groupoid_is_pstrans
  : is_pstrans id_path_groupoid_data.
Proof.
  repeat split.
  - intros X Y f g p.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    apply pathscomp0rid.
  - intros X.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    apply idpath.
  - intros X Y Z f g.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    apply idpath.
Qed.

Definition id_path_groupoid
  : pstrans
      (comp_psfunctor ⦃ I ⦄ path_groupoid)
      (comp_psfunctor path_groupoid (⟦ I ⟧)).
Proof.
  use make_pstrans.
  - exact id_path_groupoid_data.
  - exact id_path_groupoid_is_pstrans.
Defined.
