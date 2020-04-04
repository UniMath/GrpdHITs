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
Require Import displayed_algebras.total_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

Section Equalizer.
  Context {Σ : hit_signature}
          {A B : hit_algebra_one_types Σ}
          (f g : A --> B).

  Definition equalizer_disp_alg
    : disp_algebra A.
  Proof.
    use set_disp_algebra.
    - exact (λ z, pr111 f z = pr111 g z).
    - abstract
        (intro x ;
         exact (one_type_isofhlevel (pr111 B) (pr111 f x) (pr111 g x))).
    - admit.
    - admit.
  Admitted.
End Equalizer.

(*
Section Equalizer.
  Context {A B : one_types}
          (f g : A --> B).

  (** Equalizers in types *)
  Definition equalizer_UU
    : UU
    := ∑ a, f a = g a.

  Definition pr_equalizer_UU
    : equalizer_UU → (A : one_type)
    := λ a, pr1 a.

  Definition path_equalizer_UU
             (x : equalizer_UU)
    : f (pr_equalizer_UU x) = g (pr_equalizer_UU x)
    := pr2 x.

  Definition path_equalizer_to_path
             {x y : equalizer_UU}
             (p : x = y)
    : path_equalizer_UU x @ maponpaths g (maponpaths pr_equalizer_UU p)
      =
      maponpaths f (maponpaths pr_equalizer_UU p) @ path_equalizer_UU y.
  Proof.
    induction p ; simpl.
    apply pathscomp0rid.
  Qed.

  Definition path_equalizer
             {x y : equalizer_UU}
             (p : pr_equalizer_UU x = pr_equalizer_UU y)
             (s : path_equalizer_UU x @ maponpaths g p
                  =
                  maponpaths f p @ path_equalizer_UU y)
    : x = y.
  Proof.
    induction x as [x px] ; induction y as [y py]
    ; simpl in *.    
    induction p ; simpl in *.
    apply maponpaths.
    exact (!(pathscomp0rid _) @ s).
  Defined.

  Definition pr_path_equalizer
             {x y : equalizer_UU}
             (p : pr_equalizer_UU x = pr_equalizer_UU y)
             (s : path_equalizer_UU x @ maponpaths g p
                  =
                  maponpaths f p @ path_equalizer_UU y)
    : maponpaths pr_equalizer_UU (path_equalizer p s)
      =
      p.
  Proof.
    induction x as [x px] ; induction y as [y py]
    ; simpl in *.    
    induction p ; simpl in *.
    etrans.
    {
      apply (maponpathscomp (λ z, _ ,, z) pr_equalizer_UU).
    }
    apply maponpaths_for_constant_function.
  Qed.

  Definition test
             {x y : equalizer_UU}
             (p : pr_equalizer_UU x = pr_equalizer_UU y)
             (s : path_equalizer_UU x @ maponpaths g p
                  =
                  maponpaths f p @ path_equalizer_UU y)
    : UU.
  Proof.
    refine (path_equalizer_to_path (path_equalizer p s)
            =
            _).
    simpl.
  


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
*)
