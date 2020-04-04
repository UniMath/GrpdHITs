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
Require Import displayed_algebras.constant_display.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Section ProductsAlg.
  Context {Σ : hit_signature}
          (X Y : hit_algebra_one_types Σ).

  Definition prod_alg
    : hit_algebra_one_types Σ
    := total_algebra (const_disp_algebra X Y).

  Definition prod_alg_pr1
    : prod_alg --> X
    := projection _.

  Definition prod_alg_pr2
    : prod_alg --> Y.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - use make_hit_prealgebra_mor.
      + exact (λ z, pr2 z).
      + apply TODO.
    - apply TODO.
  Defined.

  Section ProdUMPMap.
    Variable (Z : hit_algebra_one_types Σ)
             (pr1Z : Z --> X)
             (pr2Z : Z --> Y).

    Definition prod_alg_ump_1
      : Z --> prod_alg.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - use make_hit_prealgebra_mor.
        + exact (λ z, pr111 pr1Z z ,, pr111 pr2Z z).
        + apply TODO.
      - apply TODO.
    Defined.

    Definition prod_alg_ump_1_pr1
      : prod_alg_ump_1 · prod_alg_pr1
        ==>
        pr1Z.
    Proof.
      simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
      - intro x ; apply idpath.
      - (*
        use funextsec.
        intro z ; cbn.
        unfold homotcomp, homotfun, funhomotsec ; cbn.
        rewrite !pathscomp0rid.
         *)
        apply TODO.
    Defined.

    Definition prod_alg_ump_1_pr2
      : prod_alg_ump_1 · prod_alg_pr2
        ==>
        pr2Z.
    Proof.
      simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
      - intro x ; apply idpath.
      - (*
        use funextsec.
        intro z ; cbn.
        unfold homotcomp, homotfun, funhomotsec ; cbn.
        rewrite !pathscomp0rid.
         *)
        apply TODO.
    Defined.
  End ProdUMPMap.
End ProductsAlg.
