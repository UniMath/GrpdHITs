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

Section Equalizer.
  Context {A B : one_types}
          (f g : A --> B).

  Definition equalizer : one_types.
  Proof.
    refine (make_one_type (∑ a, f a = g a) _).
    use isofhleveltotal2.
    - apply one_type_isofhlevel.
    - intro a.
      apply hlevelntosn.
      exact (one_type_isofhlevel B (f a) (g a)).
  Defined.

  Definition equalizer_inc
    : equalizer --> A
    := λ z, pr1 z.

  Definition equalizer_path
    : equalizer_inc · f ==> equalizer_inc · g
    := λ a, pr2 a.

  Section EqualizerUMP1.
    Variable (C : one_types)
             (Cinc : C --> A)
             (Cpath : Cinc · f ==> Cinc · g).

    Definition equalizer_ump_1
      : C --> equalizer
      := λ c, Cinc c ,, Cpath c.

    Definition equalizer_ump_1_inc
      : equalizer_ump_1 · equalizer_inc ==> Cinc
      := λ _, idpath _.

    Definition equalizer_ump_1_path
      : rassociator _ _ _
        • (equalizer_ump_1 ◃ equalizer_path)
        • lassociator _ _ _
        • (equalizer_ump_1_inc ▹ g)
        =
        (equalizer_ump_1_inc ▹ f) • Cpath.
    Proof.
      use funextsec ; intro c.
      cbn ; unfold homotcomp, homotfun, funhomotsec ; cbn.
      exact (pathscomp0rid _ @ pathscomp0rid _).
    Qed.
  End EqualizerUMP1.

  Section EqualizerUMP2.
    Context {C : one_types}
            {Cinc : C --> A}
            {Cpath : Cinc · f ==> Cinc · g}
            (φ ψ : C --> equalizer)
            (φinc : φ · equalizer_inc ==> Cinc)
            (ψinc : ψ · equalizer_inc ==> Cinc)
            (φpath : rassociator _ _ _
                     • (φ ◃ equalizer_path)
                     • lassociator _ _ _
                     • (φinc ▹ g)
                     =
                     (φinc ▹ f) • Cpath)
            (ψpath : rassociator _ _ _
                     • (ψ ◃ equalizer_path)
                     • lassociator _ _ _
                     • (ψinc ▹ g)
                     =
                     (ψinc ▹ f) • Cpath).

    Definition equalizer_ump_2
      : φ ==> ψ.
    Proof.
      intro c.
      use total2_paths_f.
      - exact (φinc c @ !(ψinc c)).
      - admit.
    Admitted.
  End EqualizerUMP2.
End Equalizer.
