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

Definition maponpaths_poly_homot
           {P : poly_code}
           {X Y Z : UU}
           {f g : X → Y}
           (h : Y → Z)
           (p : f ~ g)
           (x : poly_act P X)
  : maponpaths
      (poly_map P h)
      (poly_homot P p x)
    =
    poly_comp _ _ _ _
    @ poly_homot P (λ z, maponpaths h (p z)) x
    @ !(poly_comp _ _ _ _).
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact (!(pathscomp0rid _)).
  - induction x as [x | x] ; simpl.
    + refine (maponpathscomp inl (coprodf _ _) _ @ _).
      refine (!(maponpathscomp (poly_map _ _) inl _) @ _).
      refine (maponpaths (maponpaths inl) (IHP₁ x) @ _).
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      apply (maponpathsinv0 inl).
    + refine (maponpathscomp inr (coprodf _ _) _ @ _).
      refine (!(maponpathscomp (poly_map _ _) inr _) @ _).
      refine (maponpaths (maponpaths inr) (IHP₂ x) @ _).
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      apply (maponpathsinv0 inr).
  - simpl.
    refine (!(maponpaths_pathsdirprod _ _ _ _) @ _).
    refine (paths_pathsdirprod (IHP₁ _) (IHP₂ _) @ _).
    refine (!_).
    refine (maponpaths (λ z, _ @ (_ @ z)) (pathsdirprod_inv _ _) @ _).
    refine (maponpaths (λ z, _ @ z) (pathsdirprod_concat _ _ _ _) @ _).
    exact (pathsdirprod_concat _ _ _ _).
Qed.

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

    Definition equifier_ump_1_preserves_point
      : preserves_point equifier_ump_1_comp.
    Proof.
      intro x.
      use PathOverToTotalPath'.
      - exact (equifier_ump_1_preserves_point_pr1 x).
      - abstract
          (apply PathOver_path_hprop; intro a;
           exact (one_type_isofhlevel (pr111 B) _ _ _ _)).
    Defined.
      
    Definition equifier_ump_1_prealg
      : pr11 C --> pr11 equifier.
    Proof.
      use make_hit_prealgebra_mor.
      - exact equifier_ump_1_comp.
      - exact equifier_ump_1_preserves_point.
    Defined.


    Definition equifier_endpoint_natural
               {P Q : poly_code}
               (e : endpoint (point_constr Σ) P Q)
               (x : poly_act P (alg_carrier C))
      : maponpaths
          (poly_map Q pr1)
          (sem_endpoint_UU_natural
             e
             (prealg_map_commute equifier_ump_1_prealg)
             x)
        @ !(total_algebra.pr1_endpoint equifier_disp_alg e _)
        =
        poly_comp _ _ _ _
        @ sem_endpoint_UU_natural e (alg_map_commute Cpr) x
        @ !(maponpaths (sem_endpoint_UU e (alg_constr A)) (poly_comp _ _ _ _)).
    Proof.
      use path_inv_rotate_lr.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q
                      | P Q R e₁ IHe₁ e₂ IHe₂
                      | P T t | C₁ C₂ h | ] ; simpl.
      - refine (!_).
        refine (pathscomp0rid _ @ _ @ pathsinv0r (poly_comp P _ _ _)).
        do 2 apply maponpaths.
        apply maponpathsidfun.
      - refine (maponpathscomp0 _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply IHe₂.
        }
        clear IHe₂.
        do 2 refine (!(path_assoc _ _ _) @ _).
        refine (_ @ path_assoc _ _ _).
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        do 2 refine (_ @ path_assoc _ _ _).
        apply maponpaths.
        do 2 refine (_ @ !(path_assoc _ _ _)).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply maponpathscomp.
          }
          unfold funcomp.
          exact (!(homotsec_natural'
                     (total_algebra.pr1_endpoint equifier_disp_alg e₂)
                     (sem_endpoint_UU_natural
                        e₁ (prealg_map_commute equifier_ump_1_prealg) x))).
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (!_).
                apply maponpathscomp.
              }
              refine (!_).
              apply maponpathsinv0.
            }
            refine (!_).
            apply maponpathscomp0.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        use path_inv_rotate_rl.
        refine (!(maponpathscomp0 _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          refine (path_assoc _ _ _ @ !_).
          apply IHe₁.
        }
        clear IHe₁.
        apply maponpathscomp.
      - exact (!(pathscomp0rid _ @ pathsinv0r _)).
      - exact (!(pathscomp0rid _ @ pathsinv0r _)).
      - refine (!(pathscomp0rid _ @ _)).
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpaths_pr1_pathsdirprod.
        }
        apply pathsinv0r.
      - refine (!(pathscomp0rid _ @ _)).
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpaths_pr2_pathsdirprod.
        }
        apply pathsinv0r.
      - refine (!(maponpaths_pathsdirprod _ _ _ _) @ _).
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                etrans.
                {
                  apply maponpaths.
                  apply maponpaths_prod_path.
                }
                apply pathsdirprod_inv.
              }
              apply pathsdirprod_concat.
            }
            apply pathsdirprod_concat.
          }
          apply pathsdirprod_concat.
        }
        refine (!_).
        exact (paths_pathsdirprod (IHe₁ _) (IHe₂ _)).
      - refine (!(pathscomp0rid _ @ _)).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_for_constant_function.
        }
        apply idpath.
      - apply idpath.
      - refine (_ @ !(pathscomp0rid _)).
        etrans.
        {
          unfold prealg_map_commute ; simpl.
          unfold equifier_ump_1_preserves_point.
          exact (maponpaths_pr1_PathOverToTotalPath'
                   (equifier_ump_1_preserves_point_pr1 x)
                   _).
        }
        unfold equifier_ump_1_preserves_point_pr1.
        apply maponpaths.
        exact (maponpathsinv0 _ _).
    Qed.

    
    Definition equifier_ump_1_preserves_path
      : preserves_path _ (prealg_map_commute equifier_ump_1_prealg).
    Proof.
      intros j x.
      refine (PathOverToTotalPath'_eta _ @ _ @ !(PathOverToTotalPath'_eta _)).
      use globe_over_to_homot.
      - unfold globe ; simpl.
        refine (maponpathscomp0
                  pr1
                  (maponpaths equifier_ump_1_comp (alg_path C j x))
                  _
                @ _).
        refine (_ @ !(maponpathscomp0 _ _ _)).
        etrans.
        {
          apply maponpaths_2.
          apply maponpathscomp.
        }
        unfold funcomp ; simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          unfold total_algebra.paths.
          apply maponpaths_pr1_PathOverToTotalPath'.
        }
        etrans.
        {
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          exact (equifier_endpoint_natural (path_left Σ j) x).
        }
        simpl.
        refine (path_assoc _ _ _ @ !_).
        use path_rotate_lr.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (equifier_endpoint_natural (path_right Σ j) x).
        }
        simpl.
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          exact (alg_map_path Cpr j x).
        }
        refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply maponpathsinv0.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply maponpathsinv0.
        }
        apply homotsec_natural'.
      - apply path_globe_over_hset.
        intro.
        apply isofhlevelsnprop.
        exact (one_type_isofhlevel (pr111 B) _ _ _ _).
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
      unfold equifier_ump_1_preserves_point, equifier_ump_1_preserves_point_pr1.
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

  Section EquifierUMP2.
    Context {C : hit_algebra_one_types Σ}
            {Cpr : C --> A}
            {Chomot : Cpr ◃ p = Cpr ◃ q}
            (φ ψ : C --> equifier)
            (φpr : φ · equifier_pr ==> Cpr)
            (ψpr : ψ · equifier_pr ==> Cpr).

    Definition equifier_ump_2_on_pr1
               (c : alg_carrier C)
      : pr1 (alg_map_carrier φ c) = pr1 (alg_map_carrier ψ c)
      := pr111 φpr c @ !(pr111 ψpr c).

    Definition equifier_ump_2_component
      : alg_map_carrier φ ~ alg_map_carrier ψ.
    Proof.
      intro c.
      use PathOverToTotalPath'.
      - exact (equifier_ump_2_on_pr1 c).
      - abstract
          (apply PathOver_path_hprop; intro a;
           exact (one_type_isofhlevel (pr111 B) _ _ _ _)).
    Defined.

    Definition equifier_ump_2_is_algebra_2cell
      : is_algebra_2cell equifier_ump_2_component.
    Proof.
      intro z.
      etrans.
      {
        apply maponpaths.
        apply PathOverToTotalPath'_eta.
      }
      unfold equifier_ump_2_component.
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
        unfold  equifier_ump_2_on_pr1.
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
            pose (eqtohomot (pr211 φpr) z) as r.
            cbn in r.
            unfold homotcomp, funhomotsec, homotfun in r.
            cbn in r.
            rewrite !pathscomp0rid in r.
            exact r.
          }
          apply maponpaths.
          etrans.
          {
            refine (!_).
            apply pathscomp_inv.
          }
          pose (eqtohomot (pr211 ψpr) z) as r.
          cbn in r.
          unfold homotcomp, funhomotsec, homotfun in r.
          cbn in r.
          rewrite !pathscomp0rid in r.
          apply maponpaths.
          exact r.
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
        etrans.
        {
          apply maponpaths_poly_homot.
        }
        apply maponpaths.
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        etrans.
        {
          refine (maponpaths (λ q, poly_homot _ q z) _).
          use funextsec.
          intro.
          apply maponpaths_pr1_PathOverToTotalPath'.
        }
        etrans.
        {
          exact (eqtohomot
                   (psfunctor_vcomp
                      (⟦ point_constr Σ ⟧)
                      (alg_2cell_carrier φpr)
                      (invhomot (alg_2cell_carrier ψpr)))
                   z).
        }
        refine (maponpaths (λ q, _ @ q) _).
        apply poly_homot_inv.
      - apply path_globe_over_hset.
        intro.
        apply isofhlevelsnprop.
        exact (one_type_isofhlevel (pr111 B) _ _ _ _).
    Qed.

    Definition equifier_ump_2
      : φ ==> ψ.
    Proof.
      use make_algebra_2cell.
      - exact equifier_ump_2_component.
      - exact equifier_ump_2_is_algebra_2cell.
    Defined.

    Definition equifier_ump_2_pr
      : equifier_ump_2 ▹ equifier_pr • ψpr = φpr.
    Proof.
      use algebra_2cell_eq.
      intro c.
      assert (maponpaths
                pr1
                (PathOverToTotalPath'
                   (equifier_ump_2_on_pr1 c)
                   (equifier_ump_2_component_subproof c))
              @ (pr111 ψpr) c
              = alg_2cell_carrier φpr c)
        as X.
      {
        etrans.
        {
          apply maponpaths_2.
          unfold PathOverToTotalPath' ; apply maponpaths_pr1_PathOverToTotalPath.
        }
        unfold equifier_ump_2_on_pr1.
        refine (!(path_assoc _ _ _) @ _ @ pathscomp0rid _).
        apply maponpaths.
        apply pathsinv0l.
      }
      exact X.
    Qed.
  End EquifierUMP2.

  Section EquifierUMPEq.
    Context {C : hit_algebra_one_types Σ}
            {Cpr : C --> A}
            {Chomot : Cpr ◃ p = Cpr ◃ q}
            (φ ψ : C --> equifier)
            (φpr : φ · equifier_pr ==> Cpr)
            (ψpr : ψ · equifier_pr ==> Cpr)
            (τ θ : φ ==> ψ)
            (τpr : τ ▹ equifier_pr • ψpr = φpr)
            (θpr : θ ▹ equifier_pr • ψpr = φpr).

    Definition equifier_ump_eq
      : τ = θ.
    Proof.
      use algebra_2cell_eq.
      intro z.
      assert (maponpaths pr1 ((pr111 τ) z)
              =
              alg_2cell_carrier φpr z @ !(pr111 ψpr z)) as r.
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
              alg_2cell_carrier φpr z @ !(pr111 ψpr z)) as s.
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
      - exact (r @ !s).
      - apply path_globe_over_hset.
        intro.
        apply isofhlevelsnprop.
        exact (one_type_isofhlevel (pr111 B) _ _ _ _).
    Qed.      
  End EquifierUMPEq.
End Equifier.


