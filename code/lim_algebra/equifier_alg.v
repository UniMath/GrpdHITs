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

Section Equifier.
  Context {A B : one_types}
          {f g : A --> B}
          (p q : f ==> g).

  Definition equifier_one_types
    : one_types.
  Proof.
    refine (make_one_type (∑ a, p a = q a) _).
    apply isofhleveltotal2.
    - apply one_type_isofhlevel.
    - intro x.
      do 2 apply hlevelntosn.
      exact (one_type_isofhlevel B (f x) (g x) (p x) (q x)).
  Defined.

  Definition equifier_inc
    : equifier_one_types --> A
    := λ a, pr1 a.

  Definition equifier_homot
    : equifier_inc ◃ p = equifier_inc ◃ q.
  Proof.
    use funextsec.
    intro a.
    exact (pr2 a).
  Qed.

  Section EquifierUMP1.
    Variable (C : one_types)
             (Cinc : C --> A)
             (Chomot : Cinc ◃ p = Cinc ◃ q).

    Definition equifier_ump_1
      : C --> equifier_one_types
      := λ c, Cinc c ,, eqtohomot Chomot c.

    Definition equifier_ump_1_inc
      : equifier_ump_1 · equifier_inc ==> Cinc
      := λ _, idpath _.
  End EquifierUMP1.

  Section EquifierUMP2.
    Context {C : one_types}
            {Cinc : C --> A}
            {Chomot : Cinc ◃ p = Cinc ◃ q}
            (φ ψ : C --> equifier_one_types)
            (φinc : φ · equifier_inc ==> Cinc)
            (ψinc : ψ · equifier_inc ==> Cinc).

    Definition equifier_ump_2
      : φ ==> ψ.
    Proof.
      intro c.
      use total2_paths_f.
      - exact (φinc c @ !(ψinc c)).
      - apply B.
    Defined.

    Definition equifier_ump_2_inc
      : (equifier_ump_2 ▹ equifier_inc) • ψinc = φinc.
    Proof.
      use funextsec ; intro c.
      cbn ; unfold homotcomp, homotfun ; cbn.
      etrans.
      {
        apply maponpaths_2.
        apply base_total2_paths.
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
    Qed.
  End EquifierUMP2.

  Section EquifierUMPEq.
    Context {C : one_types}
            {Cinc : C --> A}
            {Chomot : Cinc ◃ p = Cinc ◃ q}
            {φ ψ : C --> equifier_one_types}
            {φinc : φ · equifier_inc ==> Cinc}
            {ψinc : ψ · equifier_inc ==> Cinc}
            (ρ τ : φ ==> ψ)
            (ρinc : (ρ ▹ equifier_inc) • ψinc = φinc)
            (τinc : (τ ▹ equifier_inc) • ψinc = φinc).

    Definition equifier_ump_eq
      : ρ = τ.
    Proof.
      use funextsec ; intro c.
      pose (eqtohomot ρinc c) as r₁.
      pose (eqtohomot τinc c) as r₂.
      cbn in r₁, r₂ ; unfold homotcomp, homotfun in r₁, r₂.
    Admitted.
  End EquifierUMPEq.
End Equifier.
