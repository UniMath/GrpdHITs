(** Image of algebras *)
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


Definition TODO (A : UU) : A.
Admitted.

Definition poly_dact_UU_image
           {P : poly_code}
           {A B : UU}
           (f : A → B)
           (x : poly_act P B)
           (Hx : poly_dact_UU P (λ b, ∃ a : A, f a = b) x)
  : ∃ a : poly_act P A, poly_map P f a = x.
Proof.
  induction P as [C | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (hinhpr (tpair _ x (idpath x))).
  - exact Hx.
  - induction x as [x | x].
    + refine (hinhfun _ (IHP₁ x Hx)).
      exact (λ aeq, inl (pr1 aeq),, maponpaths inl (pr2 aeq)).
    + refine (hinhfun _ (IHP₂ x Hx)).
      exact (λ aeq, inr (pr1 aeq),, maponpaths inr (pr2 aeq)).
  - refine (@hinhuniv _
                      (∃ a : poly_act (P₁ * P₂) A, poly_map (P₁ * P₂) f a = x)
                      _
                      (IHP₁ (pr1 x) (pr1 Hx))).
    intro aeq1.
    refine (hinhfun _ (IHP₂ (pr2 x) (pr2 Hx))).
    intro aeq2.
    exact ((pr1 aeq1,, pr1 aeq2),, pathsdirprod (pr2 aeq1) (pr2 aeq2)).
Qed.

Section Image.
  Context {Σ : hit_signature}
          {A B : hit_algebra_one_types Σ}
          (f : A --> B).

  Definition image_disp_alg_constr
             (x : poly_act (point_constr Σ) (alg_carrier B))
             (Hx : poly_dact_UU
                     (point_constr Σ)
                     (λ b : alg_carrier B, ∃ a : alg_carrier A, alg_map_carrier f a = b)
                     x)
    : ∃ a : alg_carrier A, alg_map_carrier f a = alg_constr B x.
  Proof.
    refine (hinhfun _ (poly_dact_UU_image (alg_map_carrier f) x Hx)).
    intro aeq.
    refine (alg_constr A (pr1 aeq) ,, _).
    refine (alg_map_commute _ _ @ _).
    exact (maponpaths (alg_constr B) (pr2 aeq)).
  Qed.

  Definition image_disp_alg : disp_algebra B. 
  Proof.
    use prop_disp_algebra.
    - exact (λ b, ∃ a : alg_carrier A, alg_map_carrier f a = b).
    - abstract (intro b; exact (isapropishinh _)).
    - exact image_disp_alg_constr.
  Defined.


  Definition image : hit_algebra_one_types Σ
    :=  total_algebra image_disp_alg.

  Definition image_pr
    : image --> B
    := projection _.

  Definition image_inj_comp
    : alg_carrier A → alg_carrier image
    := λ a, alg_map_carrier f a,, hinhpr (a,, idpath _).

  Definition image_inj_preserves_point_pr1
             (x : poly_act (point_constr Σ) (alg_carrier A))
    : pr1 (image_inj_comp (alg_constr A x))
      =
      pr1 (prealg_constr (poly_map (point_constr Σ) image_inj_comp x)).
  Proof.
    cbn; unfold poly_pr1.      
    refine (alg_map_commute _ _ @ _).
    apply maponpaths.
    refine (! _).
    apply poly_comp.
  Defined.

  Definition image_inj_preserves_point
    : preserves_point image_inj_comp.
  Proof.
    intro x.
    use PathOverToTotalPath'.
    + exact (image_inj_preserves_point_pr1 x).
    + abstract
        (apply PathOver_path_hprop; intro a;
         exact (isapropishinh _)).
  Defined.
    
  Definition image_inj_prealg
    : pr11 A --> pr11 image.
  Proof.
    use make_hit_prealgebra_mor.
    - exact image_inj_comp.
    - exact image_inj_preserves_point.
  Defined.
  
  Definition image_endpoint_natural
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (alg_carrier A))
    : maponpaths
        (poly_map Q pr1)
        (sem_endpoint_UU_natural e (prealg_map_commute image_inj_prealg) x)
      @ !(total_algebra.pr1_endpoint image_disp_alg e _)
      =
      poly_comp _ _ _ _
      @ sem_endpoint_UU_natural e (alg_map_commute f) x
      @ !(maponpaths (sem_endpoint_UU e _) (poly_comp _ _ _ _)).
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
          refine (!_).
          exact (homotsec_natural'
                   (total_algebra.pr1_endpoint image_disp_alg e₂)
                   (sem_endpoint_UU_natural
                      e₁ (prealg_map_commute image_inj_prealg) x)).
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
          exact (maponpaths_pr1_PathOverToTotalPath'
                   (image_inj_preserves_point_pr1 x)
                   _).
        }
        unfold image_inj_preserves_point_pr1.
        apply maponpaths.
        exact (maponpathsinv0 _ _).
  Qed.
  
  Definition image_inj_preserves_path
    : preserves_path _ (prealg_map_commute image_inj_prealg).
  Proof.
      intros j x.
      refine (PathOverToTotalPath'_eta _ @ _ @ !(PathOverToTotalPath'_eta _)).
      use globe_over_to_homot.
      - unfold globe.
        refine (maponpathscomp0
                  pr1
                  (maponpaths (prealg_map_carrier image_inj_prealg) (path_alg_path (pr1 A) j x))
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
          exact (image_endpoint_natural (path_left Σ j) x).
        }
        simpl.
        refine (path_assoc _ _ _ @ !_).
        use path_rotate_lr.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (image_endpoint_natural (path_right Σ j) x).
        }
        simpl.
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          exact (alg_map_path f j x).
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
        exact (isapropishinh _).
    Qed.

    Definition image_inj
    : A --> image.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - exact image_inj_prealg.
    - exact image_inj_preserves_path.
  Defined.

End Image.
