Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.globe_over_lem.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra_map.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

(** Products in 1-types *)
Section ProductsOneTypes.
  Variable (A B : one_types).

  Definition prod_one_types
    : one_types
    := make_one_type
         (pr1 A × pr1 B)
         (isofhleveldirprod
            _ _ _
            (one_type_isofhlevel A)
            (one_type_isofhlevel B)).

  Section ProductUMP1.
    Variable (C : one_types)
             (pr1C : C --> A)
             (pr2C : C --> B).
    
    Definition prod_ump_1
      : C --> prod_one_types
      := λ c, pr1C c ,, pr2C c.

    Definition prod_ump_1_pr1
      : prod_ump_1 · pr1 ==> pr1C
      := λ _, idpath _.

    Definition prod_ump_1_pr2
      : prod_ump_1 · pr2 ==> pr2C
      := λ _, idpath _.
  End ProductUMP1.

  Section ProductUMP2.
    Context {C : one_types}
            {pr1C : C --> A}
            {pr2C : C --> B}
            (f g : C --> prod_one_types)
            (fpr1 : f · pr1 ==> pr1C) (fpr2 : f · pr2 ==> pr2C)
            (gpr1 : g · pr1 ==> pr1C) (gpr2 : g · pr2 ==> pr2C).
    
    Definition prod_ump_2
      : f ==> g
      := λ c,
         pathsdirprod
           (fpr1 c @ !(gpr1 c))
           (fpr2 c @ !(gpr2 c)).

    Definition prod_ump_2_pr1
      : (prod_ump_2 ▹ _) • gpr1 = fpr1.
    Proof.
      cbn ; unfold homotcomp, homotfun, prod_ump_2.
      use funextsec ; intro c.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_pr1_pathsdirprod.
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
    Qed.

    Definition prod_ump_2_pr2
      : (prod_ump_2 ▹ _) • gpr2 = fpr2.
    Proof.
      cbn ; unfold homotcomp, homotfun, prod_ump_2.
      use funextsec ; intro c.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_pr2_pathsdirprod.
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
    Qed.
  End ProductUMP2.

  Section ProductUMPEq.
    Context {C : one_types}
            {pr1C : C --> A}
            {pr2C : C --> B}
            {f g : C --> prod_one_types}
            {fpr1 : f · pr1 ==> pr1C} {fpr2 : f · pr2 ==> pr2C}
            {gpr1 : g · pr1 ==> pr1C} {gpr2 : g · pr2 ==> pr2C}
            (p q : f ==> g)
            (ppr1 : (p ▹ _) • gpr1 = fpr1)
            (ppr2 : (p ▹ _) • gpr2 = fpr2)
            (qpr1 : (q ▹ _) • gpr1 = fpr1)
            (qpr2 : (q ▹ _) • gpr2 = fpr2).

    Definition prod_ump_eq
      : p = q.
    Proof.
      use funextsec ; intro z.
      cbn in * ; unfold homotcomp, homotfun in *.
      refine (pathsdirprod_eta _ @ _ @ !(pathsdirprod_eta _)).
      apply paths_pathsdirprod.
      - refine (_
                @ maponpaths
                    (λ w, w @ !(gpr1 z))
                    (eqtohomot ppr1 z @ eqtohomot (!qpr1) z)
                @ _).
        + refine (!_).
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0r.
          }
          apply pathscomp0rid.
        + refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0r.
          }
          apply pathscomp0rid.
      - refine (_
                @ maponpaths
                    (λ w, w @ !(gpr2 z))
                    (eqtohomot ppr2 z @ eqtohomot (!qpr2) z)
                  @ _).
        + refine (!_).
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0r.
          }
          apply pathscomp0rid.
        + refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0r.
          }
          apply pathscomp0rid.
    Qed.
  End ProductUMPEq.
End ProductsOneTypes.
