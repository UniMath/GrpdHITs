Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Final.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.

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

Section TerminalAlgebra.
  Variable (Σ : hit_signature).

  Definition terminal_prealgebra
    : hit_prealgebra_one_types Σ.
  Proof.
    use make_hit_prealgebra.
    - exact unit.
    - apply isofhlevelsnprop.
      apply isapropunit.
    - exact (λ _, tt).
  Defined.

  Definition terminal_path_algebra
    : hit_path_algebra_one_types Σ.
  Proof.
    use make_hit_path_algebra.
    - exact terminal_prealgebra.
    - intros ; cbn.
      apply isapropunit.
  Defined.

  Definition terminal_is_algebra
    : is_hit_algebra_one_types Σ terminal_path_algebra.
  Proof.
    intros j x p.
    apply isasetunit.
  Qed.    

  Definition terminal_algebra
    : hit_algebra_one_types Σ.
  Proof.
    use make_algebra.
    - exact terminal_path_algebra.
    - exact terminal_is_algebra.
  Defined.

  Definition terminal_algebra_ump_1
    : bifinal_1cell_property terminal_algebra.
  Proof.
    intro Y.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - use make_hit_prealgebra_mor.
      + exact (λ _, tt).
      + exact (λ _, idpath _).
    - intros i j ; simpl.
      apply isasetunit.
  Defined.

  Definition terminal_algebra_ump_2
             (Y : hit_algebra_one_types Σ)
    : bifinal_2cell_property terminal_algebra Y.
  Proof.
    intros f g.
    use make_invertible_2cell.
    - abstract
        (simple refine (((_ ,, _) ,, λ _, tt) ,, tt) ;
         [ intro ; apply isapropunit
         | use funextsec ; intro ; simpl
           ; apply isasetunit]).
    - apply hit_alg_is_invertible_2cell_one_type.
  Qed.

  Definition terminal_algebra_ump_eq
             (Y : hit_algebra_one_types Σ)
    : bifinal_eq_property terminal_algebra Y.
  Proof.
    intros f g p q.
    use subtypePath.
    { intro ; apply isapropunit. }
    use subtypePath.
    { intro ; apply impred ; intro ; apply isapropunit. }
    use subtypePath.
    {
      intro ; apply disp_2cells_isaprop_alg.
    }
    use funextsec.
    intro.
    apply isasetunit.
  Qed.
  
  Definition terminal_algebra_ump
    : BiFinal (pr2 (is_univalent_2_hit_algebra_one_types Σ)).
  Proof.
    refine (terminal_algebra ,, _).
    use is_bifinal'_to_is_bifinal.
    use make_is_bifinal'.
    - exact terminal_algebra_ump_1.
    - exact terminal_algebra_ump_2.
    - exact terminal_algebra_ump_eq.
  Defined.
End TerminalAlgebra.
