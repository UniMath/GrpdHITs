(** Here we define the path groupoid pseudofuncto *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.

Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.

Require Import prelude.grpd_bicat.

Local Open Scope cat.

(** Action on objects *)
Definition one_type_to_groupoid_precategory_data
           (X : one_type)
  : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact X.
    + exact (λ x y, x = y).
  - exact idpath.
  - exact (λ _ _ _ p q, p @ q).
Defined.

Definition one_type_to_groupoid_is_precategory
           (X : one_type)
  : is_precategory (one_type_to_groupoid_precategory_data X).
Proof.
  repeat split.
  - cbn ; intros a b p.
    exact (pathscomp0rid _).
  - cbn ; intros a b c d p q r.
    exact (path_assoc p q r).
  - cbn ; intros a b c d p q r.
    exact (!(path_assoc p q r)).
Qed.

Definition one_type_to_groupoid_precategory
           (X : one_type)
  : precategory.
Proof.
  use make_precategory.
  - exact (one_type_to_groupoid_precategory_data X).
  - exact (one_type_to_groupoid_is_precategory X).
Defined.

Definition one_type_to_groupoid_category
           (X : one_type)
  : category.
Proof.
  use make_category.
  - exact (one_type_to_groupoid_precategory X).
  - cbn ; intros x y ; simpl in *.
    exact (one_type_isofhlevel X x y).
Defined.

Definition one_type_inverses
           {X : one_type}
           {x y : X}
           (p : one_type_to_groupoid_precategory X ⟦ x, y ⟧)
  : is_iso p.
Proof.
  use is_iso_qinv ; simpl in *.
  - exact (!p).
  - split ; cbn.
    + exact (pathsinv0r p).
    + exact (pathsinv0l p).
Defined.

Definition one_type_to_groupoid
           (X : one_type)
  : groupoid.
Proof.
  use make_groupoid.
  - exact (one_type_to_groupoid_category X).
  - cbn ; intros x y p.
    exact (one_type_inverses p).
Defined.

(** Action on morphisms *)
Definition function_to_functor_data
           {X Y : one_type}
           (f : X → Y)
  : functor_data (one_type_to_groupoid X) (one_type_to_groupoid Y).
Proof.
  use make_functor_data.
  - exact f.
  - exact (λ _ _ p, maponpaths f p).
Defined.

Definition function_to_functor_laws
           {X Y : one_type}
           (f : X → Y)
  : is_functor (function_to_functor_data f).
Proof.
  split.
  - intros x ; cbn.
    apply idpath.
  - intros x y z p q ; cbn.
    apply maponpathscomp0.
Qed.

Definition function_to_functor
           {X Y : one_type}
           (f : X → Y)
  : one_type_to_groupoid X ⟶ one_type_to_groupoid Y.
Proof.
  use make_functor.
  - exact (function_to_functor_data f).
  - exact (function_to_functor_laws f).
Defined.

(** Action on cells *)
Definition path_to_nattrans
           {X Y : one_type}
           {f g : X → Y}
           (p : homotsec f g)
  : function_to_functor f ⟹ function_to_functor g.
Proof.
  use make_nat_trans.
  - exact p.
  - abstract
      (intros x y q ; cbn in * ;
       induction q ; simpl ;
       refine (!_) ;
       apply pathscomp0rid).
Defined.

(** Identitor *)
Definition path_groupoid_identitor
           (X : one_type)
  : functor_identity _ ⟹ function_to_functor (λ (x : X), x).
Proof.
  use make_nat_trans.
  - exact idpath.
  - abstract
      (intros x y p ; cbn in * ;
       induction p ; cbn ;
       apply idpath).
Defined.

(** Compositor *)
Definition path_groupoid_compositor
           {X Y Z : one_type}
           (f : X → Y)
           (g : Y → Z)
  : (function_to_functor f ∙ function_to_functor g)
      ⟹
      function_to_functor (λ x, g(f x)).
Proof.
  use make_nat_trans.
  - exact (λ x, idpath (g(f x))).
  - abstract
      (intros x y p ; cbn in * ;
       induction p ; cbn ;
       apply idpath).
Defined.

(** Data of path groupoid pseudofunctor *)
Definition path_groupoid_data
  : psfunctor_data one_types grpd_bicat.
Proof.
  use make_psfunctor_data.
  - exact one_type_to_groupoid.
  - exact @function_to_functor.
  - exact @path_to_nattrans.
  - exact path_groupoid_identitor.
  - exact @path_groupoid_compositor.
Defined.

(** Laws *)
Definition path_groupoid_laws
  : psfunctor_laws path_groupoid_data.
Proof.
  repeat split.
  - intros X Y f.
    apply nat_trans_eq.
    { apply homset_property. }
    intro x ; cbn.
    apply idpath.
  - intros X Y f g h p q.
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    apply idpath.
  - intros X Y f.
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    apply idpath.
  - intros X Y f.
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    apply idpath.
  - intros W X Y Z f g h.
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    apply idpath.
  - intros X Y Z f g₁ g₂ p.
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    cbn.
    refine (!_).
    apply pathscomp0rid.
  - intros X Y Z f₁ f₂ g p.
    apply nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    cbn.
    refine (!_).
    apply pathscomp0rid.
Qed.

(** The identitor and compositor are invertible *)
Definition path_groupoid_invertible_cells
  : invertible_cells path_groupoid_data.
Proof.
  split ; intros ; apply grpd_bicat_is_invertible_2cell.
Defined.

(** The pseudofunctor *)
Definition path_groupoid
  : psfunctor one_types grpd_bicat.
Proof.
  use make_psfunctor.
  - exact path_groupoid_data.
  - exact path_groupoid_laws.
  - exact path_groupoid_invertible_cells.
Defined.
