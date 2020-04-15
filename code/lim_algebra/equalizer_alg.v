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

Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.globe_over_lem.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.

Local Open Scope cat.

Definition poly_dact_UU_on_eq
           {P : poly_code}
           {A B : UU}
           {f g : A → B}
           (x : poly_act P A)
           (Hx : poly_dact_UU P (λ z, f z = g z) x)
  : poly_map P f x = poly_map P g x.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact Hx.
  - induction x as [x | x].
    + exact (maponpaths inl (IHP₁ x Hx)).
    + exact (maponpaths inr (IHP₂ x Hx)).
  - exact (pathsdirprod (IHP₁ _ (pr1 Hx)) (IHP₂ _ (pr2 Hx))).
Defined.

Definition paths_one_type
           {A : one_type}
           (a₁ a₂ : A)
  : one_type.
Proof.
  use make_one_type.
  - exact (a₁ = a₂).
  - apply hlevelntosn.
    exact (one_type_isofhlevel A a₁ a₂).
Defined.

Definition poly_dact_UU_on_eq_lem
           {P : poly_code}
           {Z A B : one_type}
           {f g : A → B}
           (hpr1 : Z → A)
           (hpr2 : ∏ (z : Z), f(hpr1 z) = g(hpr1 z))
           (x : poly_act P Z)
           (HP : ∏ z, isofhlevel 3 (f z = g z))
  : @poly_dact_UU_on_eq
      P
      A B f g
      (poly_pr1 P (poly_map P _ x))
      (@poly_pr2
         P A (λ z, make_one_type (f z = g z) (HP z))
         (poly_map P (λ z, hpr1 z ,, hpr2 z) x))
    =
    maponpaths (poly_map P f) (poly_comp _ _ _ _)
    @ poly_comp _ _ _ _
    @ poly_homot P hpr2 _
    @ !(poly_comp _ _ _ _)
    @ maponpaths (poly_map P g) (!(poly_comp _ _ _ _)).
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact (!(pathscomp0rid _)).
  - induction x as [x | x].
    + simpl.
      refine (maponpaths (maponpaths inl) (IHP₁ x) @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          refine (maponpathscomp inl (coprodf _ _) _ @ _).
          exact (!(maponpathscomp (poly_map P₁ f) inl _)).
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  exact (!(maponpathsinv0 _ _)).
                }
                refine (maponpathscomp inl (coprodf _ _) _ @ _).
                exact (!(maponpathscomp (poly_map P₁ g) inl _)).
              }
              etrans.
              {
                apply maponpaths_2.
                exact (!(maponpathsinv0 inl _)).
              }
              exact (!(maponpathscomp0 inl _ _)).
            }
            exact (!(maponpathscomp0 inl _ _)).
          }
          exact (!(maponpathscomp0 inl _ _)).
        }
        exact (!(maponpathscomp0 inl _ _)).
      }
      apply idpath.
    + simpl.
      refine (maponpaths (maponpaths inr) (IHP₂ x) @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          refine (maponpathscomp inr (coprodf _ _) _ @ _).
          exact (!(maponpathscomp (poly_map P₂ f) inr _)).
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  exact (!(maponpathsinv0 _ _)).
                }
                refine (maponpathscomp inr (coprodf _ _) _ @ _).
                exact (!(maponpathscomp (poly_map P₂ g) inr _)).
              }
              etrans.
              {
                apply maponpaths_2.
                exact (!(maponpathsinv0 inr _)).
              }
              exact (!(maponpathscomp0 inr _ _)).
            }
            exact (!(maponpathscomp0 inr _ _)).
          }
          exact (!(maponpathscomp0 inr _ _)).
        }
        exact (!(maponpathscomp0 inr _ _)).
      }
      apply idpath.
  - simpl.
    refine (paths_pathsdirprod (IHP₁ _) (IHP₂ _) @ _).
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpaths_pathsdirprod _ _ _ _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                apply pathsdirprod_inv.
              }
              exact (!(maponpaths_pathsdirprod _ _ _ _)).
            }
            etrans.
            {
              apply maponpaths_2.
              apply pathsdirprod_inv.
            }
            apply pathsdirprod_concat.
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    apply idpath.
Qed.

Definition TODO {A : UU} : A.
Admitted.

  
Section Equalizer.
  Context {Σ : hit_signature}
          {A B : hit_algebra_one_types Σ}
          (f g : A --> B).

  Definition equalizer_disp_alg_constr
             (x : poly_act (point_constr Σ) (alg_carrier A))
             (Hx : poly_dact_UU
                     (point_constr Σ)
                     (λ z : alg_carrier A, alg_map_carrier f z = alg_map_carrier g z)
                     x)
    : alg_map_carrier f (alg_constr A x) = alg_map_carrier g (alg_constr A x).
  Proof.
    exact (alg_map_commute f x
           @ maponpaths (alg_constr B) (poly_dact_UU_on_eq x Hx)
           @ !(alg_map_commute g x)).
  Defined.
  
  Definition equalizer_disp_alg
    : disp_algebra A.
  Proof.
    use set_disp_algebra.
    - exact (λ z, alg_map_carrier f z = alg_map_carrier g z).
    - abstract
        (intro x ;
         exact (one_type_isofhlevel (pr111 B) _ _)).
    - exact equalizer_disp_alg_constr.
    - apply TODO.
  Defined.
  
  Definition equalizer
    : hit_algebra_one_types Σ
    := total_algebra equalizer_disp_alg.

  Definition equalizer_pr
    : equalizer --> A
    := projection _.

  Definition equalizer_path_component
    : alg_map_carrier (equalizer_pr · f) ~ alg_map_carrier (equalizer_pr · g)
    := λ a, pr2 a.

  Definition equalizer_path_is_alg_2cell_help
             {P : poly_code}
    : ∏ (x : poly_act P (alg_carrier equalizer)),
      poly_comp P pr1 (alg_map_carrier f) x
      @ poly_homot P (λ z, pr2 z) x
      =
      poly_dact_UU_on_eq (poly_pr1 P x) (poly_pr2 P x)
      @ poly_comp P pr1 (alg_map_carrier g) x.
  Proof.
    intro x.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - exact (!(pathscomp0rid _)).
    - induction x as [x | x].
      + simpl.
        etrans.
        {
          refine (!_).
          apply (maponpathscomp0 inl).
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (maponpathscomp0 inl).
        }
        apply maponpaths.
        exact (!(IHP₁ x)).
      + simpl.
        etrans.
        {
          refine (!_).
          apply (maponpathscomp0 inr).
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (maponpathscomp0 inr).
        }
        apply maponpaths.
        exact (!(IHP₂ x)).
    - simpl.
      refine (pathsdirprod_concat _ _ _ _ @ _ @ !(pathsdirprod_concat _ _ _ _)).
      exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
  Qed.
  
  Definition equalizer_path_is_alg_2cell
    : is_algebra_2cell equalizer_path_component.
  Proof.
    intro a.
    cbn ; unfold homotcomp, homotfun, funhomotsec ; cbn.
    rewrite !pathscomp0rid.
    unfold equalizer_disp_alg_constr.
    rewrite <- !path_assoc.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite path_assoc.
      apply maponpaths_2.
      apply pathsinv0l.
    }
    cbn.
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    refine (!_).
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    apply maponpaths.
    apply equalizer_path_is_alg_2cell_help.
  Qed.
  
  Definition equalizer_path
    : equalizer_pr · f ==> equalizer_pr · g.
  Proof.
    use make_algebra_2cell.
    - exact equalizer_path_component.
    - exact equalizer_path_is_alg_2cell.
  Defined.
  
  Section EqualizerUMP1.
    Variable (C : hit_algebra_one_types Σ)
             (Cpr : C --> A)
             (Cpath : Cpr · f ==> Cpr · g).

    Definition equalizer_ump_1_comp
      : alg_carrier C → alg_carrier equalizer
      := λ c, alg_map_carrier Cpr c ,, pr111 Cpath c.

    Definition equalizer_ump_1_preserves_point_pr1
               (x : poly_act (point_constr Σ) (alg_carrier C))
      : pr1 (equalizer_ump_1_comp (alg_constr C x))
        =
        pr1 (prealg_constr (poly_map (point_constr Σ) equalizer_ump_1_comp x)).
    Proof.
      cbn ; unfold poly_pr1.
      refine (alg_map_commute Cpr x @ _).
      apply maponpaths.
      refine (!_).
      refine (poly_comp _ _ _ _ @ _).
      apply poly_homot.
      intro.
      apply idpath.
    Defined.

    Definition equalizer_ump_1_preserves_point_pr2
               (x : poly_act (point_constr Σ) (alg_carrier C))
      : PathOver
          (pr2 (equalizer_ump_1_comp (prealg_constr x)))
          (pr2 (prealg_constr (poly_map (point_constr Σ) equalizer_ump_1_comp x)))
          (equalizer_ump_1_preserves_point_pr1 x).
    Proof.
      simpl.
      pose (eqtohomot (pr211 Cpath) x) as p.
      cbn in p.
      unfold homotcomp, homotfun, funhomotsec in p.
      cbn in p.
      rewrite !pathscomp0rid in p.
      apply map_PathOver ; unfold square.
      rewrite !path_assoc in p.
      pose (path_inv_rotate_rr _ _ _ p) as p'.
      pose (path_inv_rotate_rr _ _ _ p') as p''.
      unfold disp_alg_constr.
      simpl.
      unfold equalizer_disp_alg_constr, equalizer_ump_1_preserves_point_pr1.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpathscomp0.
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        exact p''.
      }
      clear p'' p' p.
      rewrite maponpathscomp0.
      rewrite <- !path_assoc.
      apply maponpaths.
      etrans.
      {
        do 4 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply maponpathscomp.
        }
        refine (!_).
        apply (homotsec_natural' (invhomot (alg_map_commute g))).
      }
      rewrite !path_assoc ; unfold invhomot.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathscomp.
        }
        apply (homotsec_natural' (alg_map_commute f)).
      }
      rewrite <- !path_assoc.
      apply maponpaths.
      rewrite <- !maponpathsinv0.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathscomp _ (alg_constr B)).
      }
      rewrite <- !maponpathscomp0.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        refine (!_).
        apply (maponpathscomp _ (alg_constr B)).
      }
      rewrite <- !maponpathscomp0.
      apply maponpaths.
      etrans.
      {
        do 5 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply (eqtohomot (psfunctor_id2 (⟦ point_constr Σ ⟧) _)).
        }
        apply pathscomp0rid.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply (eqtohomot (psfunctor_id2 (⟦ point_constr Σ ⟧) _)).
        }
        apply pathscomp0rid.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpathsinv0.
      }
      use path_inv_rotate_ll.
      apply poly_dact_UU_on_eq_lem.
    Time Qed.

    Definition equalizer_ump_1_preserves_point
      : preserves_point equalizer_ump_1_comp.
    Proof.
      intro x.
      use PathOverToTotalPath'.
      - exact (equalizer_ump_1_preserves_point_pr1 x).
      - exact (equalizer_ump_1_preserves_point_pr2 x).
    Defined.

    Definition equalizer_ump_1_prealg
      : pr11 C --> pr11 equalizer.
    Proof.
      use make_hit_prealgebra_mor.
      - exact equalizer_ump_1_comp.
      - exact equalizer_ump_1_preserves_point.
    Defined.

    Definition equalizer_ump_1_preserves_path
      : preserves_path _ (prealg_map_commute equalizer_ump_1_prealg).
    Proof.
      intros j x.
      apply TODO.
    Qed.

    Definition equalizer_ump_1
      : C --> equalizer.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - exact equalizer_ump_1_prealg.
      - exact equalizer_ump_1_preserves_path.
    Defined.

    Definition equalizer_ump_pr1_component
      : alg_map_carrier (equalizer_ump_1 · equalizer_pr) ~ alg_map_carrier Cpr
      := λ _, idpath _.

    Definition equalizer_ump_1_is_algebra_2cell
      : is_algebra_2cell equalizer_ump_pr1_component.
    Proof.
      intro.
      cbn -[PathOverToTotalPath']
      ; unfold homotcomp, homotfun, funhomotsec
      ; cbn -[PathOverToTotalPath'].
      rewrite !pathscomp0rid.
      refine (!_).
      etrans.      
      {
        do 2 apply maponpaths_2.
        unfold equalizer_ump_1_preserves_point, PathOverToTotalPath'
        ; apply maponpaths_pr1_PathOverToTotalPath.
      }
      unfold equalizer_ump_1_preserves_point_pr1.
      rewrite <- !path_assoc.
      refine (_ @ pathscomp0rid _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathscomp0.
      }
      etrans.
      {
        refine (!_).
        apply maponpathscomp0.
      }
      refine (_ @ maponpaths_idpath).
      apply maponpaths.
      apply pathsinv0l.
    Qed.

    Definition equalizer_ump_1_pr
      : equalizer_ump_1 · equalizer_pr ==> Cpr.
    Proof.
      use make_algebra_2cell.
      - exact equalizer_ump_pr1_component.
      - exact equalizer_ump_1_is_algebra_2cell.
    Defined.
    
    Definition equalizer_ump_1_path
      : rassociator _ _ _
        • (equalizer_ump_1 ◃ equalizer_path)
        • lassociator _ _ _
        • (equalizer_ump_1_pr ▹ g)
        =
        (equalizer_ump_1_pr ▹ f) • Cpath.
    Proof.
      use subtypePath.
      { intro ; apply isapropunit. }
      use subtypePath.
      { intro ; use impred ; intro ; apply isapropunit. }
      use subtypePath.
      { intro ; apply one_types. }
      use funextsec ; intro c.
      cbn ; unfold homotcomp, homotfun, funhomotsec ; cbn.
      exact (pathscomp0rid _ @ pathscomp0rid _).
    Qed.
  End EqualizerUMP1.

  Section EqualizerUMP2.
    Context {C : hit_algebra_one_types Σ}
            {Cpr : C --> A}
            {Cpath : Cpr · f ==> Cpr · g}
            (φ ψ : C --> equalizer)
            (φpr : φ · equalizer_pr ==> Cpr)
            (ψpr : ψ · equalizer_pr ==> Cpr)
            (φpath : rassociator _ _ _
                     • (φ ◃ equalizer_path)
                     • lassociator _ _ _
                     • (φpr ▹ g)
                     =
                     (φpr ▹ f) • Cpath)
            (ψpath : rassociator _ _ _
                     • (ψ ◃ equalizer_path)
                     • lassociator _ _ _
                     • (ψpr ▹ g)
                     =
                     (ψpr ▹ f) • Cpath).

    Definition equalizer_ump_2_on_pr1
               (c : alg_carrier C)
      : pr1 (alg_map_carrier φ c) = pr1 (alg_map_carrier ψ c)
      := pr111 φpr c @ !(pr111 ψpr c).

    Definition equalizer_ump_2_on_pr2
               (c : alg_carrier C)
      : PathOver
          (pr2 (alg_map_carrier φ c))
          (pr2 (alg_map_carrier ψ c))
          (equalizer_ump_2_on_pr1 c).
    Proof.
      apply map_PathOver ; unfold square.
      assert (equalizer_path_component (alg_map_carrier φ c)
              @ maponpaths (alg_map_carrier g) (alg_2cell_carrier φpr c)
              =
              maponpaths (alg_map_carrier f) (alg_2cell_carrier φpr c)
              @ alg_2cell_carrier Cpath c)
        as X.
      {
        refine (_ @ alg_2cell_eq_component φpath c).
        cbn.
        unfold homotcomp, homotfun, funhomotsec.
        cbn.
        rewrite pathscomp0rid.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply maponpathscomp0.
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        exact X.
      }
      clear X.
      refine (!(path_assoc _ _ _) @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp0.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpathsinv0.
      }
      use path_inv_rotate_ll.
      refine (_ @ !(path_assoc _ _ _)).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpathsinv0.
      }
      use path_inv_rotate_lr.
      assert (equalizer_path_component (alg_map_carrier ψ c)
              @ maponpaths (alg_map_carrier g) (alg_2cell_carrier ψpr c)
              =
              maponpaths (alg_map_carrier f) (alg_2cell_carrier ψpr c)
              @ alg_2cell_carrier Cpath c)
        as X.
      {
        refine (_ @ alg_2cell_eq_component ψpath c).
        cbn.
        unfold homotcomp, homotfun, funhomotsec.
        cbn.
        rewrite pathscomp0rid.
        apply idpath.
      }
      exact (!X).
    Qed.

    Definition equalizer_ump_2_component
      : alg_map_carrier φ ~ alg_map_carrier ψ.
    Proof.
      intro c.
      use PathOverToTotalPath'.
      - exact (equalizer_ump_2_on_pr1 c).
      - exact (equalizer_ump_2_on_pr2 c).
    Defined.

    Definition equalizer_ump_2_is_algebra_2cell
      : is_algebra_2cell equalizer_ump_2_component.
    Proof.
      intro z.
      etrans.
      {
        apply maponpaths.
        apply PathOverToTotalPath'_eta.
      }
      unfold equalizer_ump_2_component.
      etrans.
      {
        apply PathOverToTotalPath'_comp.
      }
      refine (_ @ !(PathOverToTotalPath'_eta _)).
      use globe_over_to_homot.
      - unfold globe ; simpl.
        refine (!_).
        etrans.
        {
          etrans.
          {
            exact (maponpathscomp0 pr1 (alg_map_commute φ z) (maponpaths _ _)).
          }
          etrans.
          {
            apply maponpaths.
            apply maponpathscomp.
          }
          unfold funcomp.
          simpl.
          apply idpath.
        }
        refine (!_).
        unfold  equalizer_ump_2_on_pr1.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              exact (!(pathscomp0rid _)).
            }
            apply maponpaths.
            exact (!(pathsinv0r (alg_map_commute Cpr z))).
          }
          etrans.
          {
            etrans.
            {
              apply maponpaths_2.
              exact (path_assoc _ _ _).
            }
            exact (!(path_assoc _ _ _)).
          }
          etrans.
          {
            apply maponpaths_2.
            pose (eqtohomot (pr211 φpr) z) as p.
            cbn in p.
            unfold homotcomp, funhomotsec, homotfun in p.
            cbn in p.
            rewrite !pathscomp0rid in p.
            exact p.
          }
          apply maponpaths.
          etrans.
          {
            refine (!_).
            apply pathscomp_inv.
          }
          pose (eqtohomot (pr211 ψpr) z) as p.
          cbn in p.
          unfold homotcomp, funhomotsec, homotfun in p.
          cbn in p.
          rewrite !pathscomp0rid in p.
          apply maponpaths.
          exact p.
        }
        rewrite !pathscomp_inv.
        rewrite <- !path_assoc.
        apply maponpaths.
        rewrite pathsinv0l, pathscomp0rid.
        rewrite <- !maponpathsinv0.
        rewrite <- !maponpathscomp0.
        refine (!_).
        etrans.
        {
          refine (!_).
          apply maponpathscomp.
        }
        apply maponpaths.
        unfold poly_pr1.
        apply TODO.
      - apply (one_type_isofhlevel (pr111 B)).
    Time Qed.

    Definition equalizer_ump_2
      : φ ==> ψ.
    Proof.
      use make_algebra_2cell.
      - exact equalizer_ump_2_component.
      - exact equalizer_ump_2_is_algebra_2cell.
    Defined.

    Definition equalizer_ump_2_pr
      : equalizer_ump_2 ▹ equalizer_pr • ψpr = φpr.
    Proof.
      use algebra_2cell_eq.
      intro c.
      cbn.
      unfold homotcomp, homotfun, equalizer_ump_2_component.
      etrans.
      {
        apply maponpaths_2.
        unfold PathOverToTotalPath' ; apply maponpaths_pr1_PathOverToTotalPath.
      }
      unfold equalizer_ump_2_on_pr1.
      refine (!(path_assoc _ _ _) @ _ @ pathscomp0rid _).
      apply maponpaths.
      apply pathsinv0l.
    Qed.
  End EqualizerUMP2.

  Section EqualizerUMPEq.
    Context {C : hit_algebra_one_types Σ}
            {Cpr : C --> A}
            {Cpath : Cpr · f ==> Cpr · g}
            (φ ψ : C --> equalizer)
            (φpr : φ · equalizer_pr ==> Cpr)
            (ψpr : ψ · equalizer_pr ==> Cpr)
            (φpath : rassociator _ _ _
                     • (φ ◃ equalizer_path)
                     • lassociator _ _ _
                     • (φpr ▹ g)
                     =
                     (φpr ▹ f) • Cpath)
            (ψpath : rassociator _ _ _
                     • (ψ ◃ equalizer_path)
                     • lassociator _ _ _
                     • (ψpr ▹ g)
                     =
                     (ψpr ▹ f) • Cpath)
            (τ θ : φ ==> ψ)
            (τpr : τ ▹ equalizer_pr • ψpr = φpr)
            (θpr : θ ▹ equalizer_pr • ψpr = φpr).

    Definition equalizer_ump_eq
      : τ = θ.
    Proof.
      use algebra_2cell_eq.
      intro z.
      assert (maponpaths pr1 ((pr111 τ) z)
              =
              alg_2cell_carrier φpr z @ !(pr111 ψpr z)) as p.
      {
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(alg_2cell_eq_component τpr z)).
        }
        refine (!(path_assoc _ _ _) @ _ @ pathscomp0rid _).
        apply maponpaths.
        apply pathsinv0r.
      }
      assert (maponpaths pr1 ((pr111 θ) z)
              =
              alg_2cell_carrier φpr z @ !(pr111 ψpr z)) as q.
      {
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(alg_2cell_eq_component θpr z)).
        }
        refine (!(path_assoc _ _ _) @ _ @ pathscomp0rid _).
        apply maponpaths.
        apply pathsinv0r.
      }
      refine (PathOverToTotalPath'_eta _ @ _ @ !(PathOverToTotalPath'_eta _)).
      use globe_over_to_homot.
      - exact (p @ !q).
      - apply (one_type_isofhlevel (pr111 B)).
    Qed.
  End EqualizerUMPEq.
End Equalizer.
