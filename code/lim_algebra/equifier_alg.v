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
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

Definition poly_dact_UU_on_homot
           {P : poly_code}
           {A B : UU}
           {f g : A → B}
           {p q : f ~ g}
           (x : poly_act P A)
           (Hx : poly_dact_UU P (λ z, p z = q z) x)
  : poly_homot P p x = poly_homot P q x.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact Hx.
  - induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (IHP₁ x Hx)).
    + exact (maponpaths (maponpaths inr) (IHP₂ x Hx)).
  - refine (maponpaths (pathsdirprod (poly_homot P₁ p (pr1 x))) (IHP₂ _ (pr2 Hx)) @ _).
    exact (maponpaths (λ z,  pathsdirprod z (poly_homot P₂ q (pr2 x))) (IHP₁ _ (pr1 Hx))). 
Defined.

Definition TODO {A : UU} : A.
Admitted.

Section Equifier.
  Context {Σ : hit_signature}
          {A B : hit_algebra_one_types Σ}
          {f g : A --> B}
          (p q : f ==> g).

  Definition equifier_disp_alg_constr
             (x : poly_act (point_constr Σ) (alg_carrier A))
             (Hx : poly_dact_UU
                     (point_constr Σ)
                     (λ a : alg_carrier A, alg_2cell_carrier p a = alg_2cell_carrier q a)
                     x)
    : alg_2cell_carrier p (alg_constr A x) = alg_2cell_carrier q (alg_constr A x).
  Proof.
    refine (!(pathscomp0rid _) @ _).
    refine (maponpaths (λ z, alg_2cell_carrier p (alg_constr A x) @ z)
                       (!(pathsinv0r (alg_map_commute g x))) @ _).
    refine (path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, z @ ! alg_map_commute g x) (alg_2cell_commute p x) @ _).
    refine (! path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, alg_map_commute f x
                                             @ maponpaths (alg_constr B) z
                                             @ ! alg_map_commute g x)
                       (poly_dact_UU_on_homot x Hx) @ _).
    refine (path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, z @ ! alg_map_commute g x) (! alg_2cell_commute q x) @ _).
    refine (! path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, alg_2cell_carrier q (alg_constr A x) @ z)
                       (pathsinv0r (alg_map_commute g x)) @ _).
    exact (pathscomp0rid _).
  Qed.
  
  Definition equifier_disp_alg
    : disp_algebra A.
  Proof.
    use prop_disp_algebra.
    - exact (λ a, alg_2cell_carrier p a = alg_2cell_carrier q a).
    - abstract (intro a ; exact (one_type_isofhlevel _ _ _ _ _)).
    - exact equifier_disp_alg_constr.
  Defined.

  Definition equifier
    : hit_algebra_one_types Σ
    := total_algebra equifier_disp_alg.

  Definition equifier_pr
    : equifier --> A
    := projection _.

  Definition equifier_homot_component
    : alg_2cell_carrier (equifier_pr ◃ p) ~ alg_2cell_carrier (equifier_pr ◃ q).
  Proof.
    exact pr2.
  Qed.

  Definition equifier_homot
    : equifier_pr ◃ p = equifier_pr ◃ q.
  Proof.
    use algebra_2cell_eq.
    exact equifier_homot_component.
  Qed.

  Section EquifierUMP1.
    Variable (C : hit_algebra_one_types Σ)
             (Cpr : C --> A)
             (Chomot : Cpr ◃ p = Cpr ◃ q).
    
    Definition equifier_ump_1_comp
      : alg_carrier C → alg_carrier equifier
      := λ c, alg_map_carrier Cpr c ,, maponpaths (λ z, alg_2cell_carrier z c) Chomot.

    Definition equifier_ump_1_preserves_point_pr1
               (x : poly_act (point_constr Σ) (alg_carrier C))
      : pr1 (equifier_ump_1_comp (alg_constr C x))
        =
        pr1 (prealg_constr (poly_map (point_constr Σ) equifier_ump_1_comp x)).
    Proof.
      cbn; unfold poly_pr1.      
      refine (alg_map_commute Cpr x @ _).
      apply maponpaths.
      refine (! _).
      apply poly_comp.
    Defined.

    Definition equifier_ump_1_preserves_point_pr2
               (x : poly_act (point_constr Σ) (alg_carrier C))
      : PathOver
          (pr2 (equifier_ump_1_comp (prealg_constr x)))
          (pr2 (prealg_constr (poly_map (point_constr Σ) equifier_ump_1_comp x)))
          (equifier_ump_1_preserves_point_pr1 x).
    Proof.
      apply PathOver_path_hprop.
      intro a.
      exact (one_type_isofhlevel (pr111 B)
                                 (alg_map_carrier f a)
                                 (alg_map_carrier g a)
                                 (alg_2cell_carrier p a)
                                 (alg_2cell_carrier q a)).
    Qed.
      
    Definition equifier_ump_1_preserves_point
      : preserves_point equifier_ump_1_comp.
    Proof.
      intro x.
      use PathOverToTotalPath'.
      - exact (equifier_ump_1_preserves_point_pr1 x).
      - exact (equifier_ump_1_preserves_point_pr2 x).
    Defined.
      
    Definition equifier_ump_1_prealg
      : pr11 C --> pr11 equifier.
    Proof.
      use make_hit_prealgebra_mor.
      - exact equifier_ump_1_comp.
      - exact equifier_ump_1_preserves_point.
    Defined.

    Definition equifier_ump_1_preserves_path
      : preserves_path _ (prealg_map_commute equifier_ump_1_prealg).
    Proof.
      intros j x.
      apply TODO.
    Qed.
    
    Definition equifier_ump_1
      : C --> equifier.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - exact equifier_ump_1_prealg.
      - exact equifier_ump_1_preserves_path.
    Defined.

    Definition equifier_ump_pr1_component
      : alg_map_carrier (equifier_ump_1 · equifier_pr) ~ alg_map_carrier Cpr
      := λ _, idpath _.

    Definition equifier_ump_1_is_algebra_2cell
      : is_algebra_2cell equifier_ump_pr1_component.
    Proof.
      intro.
      unfold equifier_ump_pr1_component.
      refine (pathscomp0lid _ @ _).      
      refine (_ @
                maponpaths (λ x, _ @ maponpaths (alg_constr A) x)
                (! eqtohomot (psfunctor_id2 (⟦ point_constr Σ ⟧) _) _)).
      refine (_ @ ! pathscomp0rid _).
      unfold equifier_ump_1, equifier_pr.
      cbn.
      unfold homotcomp, homotfun, funhomotsec.
      rewrite !pathscomp0rid, pathscomp0lid.
      unfold equifier_ump_1_preserves_point.
      unfold equifier_ump_1_preserves_point_pr1.
      Search maponpaths.
      Check maponpaths_pr1_PathOverToTotalPath.
      refine (! (maponpaths (λ x, x @ _) _ @ _)).
      - apply maponpaths_pr1_PathOverToTotalPath.
      - refine (! path_assoc _ _ _ @ _ @ pathscomp0rid _).
        apply (maponpaths (λ x, _ @ x)).
        refine (! maponpathscomp0 (alg_constr A) _ _ @ _).
        refine (_@_).
        + apply maponpaths.
          exact (pathsinv0l _).
        + apply idpath.
    Qed.
    
    Definition equifier_ump_1_pr
      : equifier_ump_1 · equifier_pr ==> Cpr.
    Proof.
      use make_algebra_2cell.
      - exact equifier_ump_pr1_component.
      - exact equifier_ump_1_is_algebra_2cell.
    Defined.
    
  End EquifierUMP1.
End Equifier.


