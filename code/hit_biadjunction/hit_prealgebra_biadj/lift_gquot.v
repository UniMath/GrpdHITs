(* Lifting pseudofunctors to pseudofunctors on algebras *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import hit_biadjunction.gquot_natural.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

Local Arguments nat_trans_comp {_ _ _ _ _} _ _.

Local Definition TODO {A : UU} : A.
Admitted.
(*
Definition idtoiso_inl
           (P₁ P₂ : poly_code)
           {G : groupoid}
           {a₁ a₂ : poly_act_groupoid P₁ G}
           (p : a₁ = a₂)
  : pr1 (@idtoiso (⦃ P₁ + P₂ ⦄ G : groupoid)
                  (inl a₁) (inl a₂)
                  (maponpaths inl p))
    =
    pr1 (@idtoiso (⦃ P₁ ⦄ G : groupoid) a₁ a₂ p).
Proof.
  induction p.
  apply idpath.
Qed.

Definition idtoiso_inr
           (P₁ P₂ : poly_code)
           {G : groupoid}
           {a₁ a₂ : poly_act_groupoid P₂ G}
           (p : a₁ = a₂)
  : pr1 (@idtoiso (⦃ P₁ + P₂ ⦄ G : groupoid)
                  (inr a₁) (inr a₂)
                  (maponpaths inr p))
    =
    pr1 (@idtoiso (⦃ P₂ ⦄ G : groupoid) a₁ a₂ p).
Proof.
  induction p.
  apply idpath.
Qed.

Definition idtoiso_pathsdirprod
           (P₁ P₂ : poly_code)
           {G : groupoid}
           {a₁ a₂ : poly_act_groupoid P₁ G}
           {b₁ b₂ : poly_act_groupoid P₂ G}
           (p : a₁ = a₂) (q : b₁ = b₂)
  : pr1 (@idtoiso (⦃ P₁ * P₂ ⦄ G : groupoid)
                  (a₁ ,, b₁) (a₂ ,, b₂)
                  (pathsdirprod p q))
    =
    (pr1 (@idtoiso (⦃ P₁ ⦄ G : groupoid) a₁ a₂ p)
    ,,
    pr1 (@idtoiso (⦃ P₂ ⦄ G : groupoid) b₁ b₂ q)).
Proof.
  induction p ; induction q.
  apply idpath.
Qed.
*)

Definition test1
           {P : poly_code}
           {X : groupoid}
           (z : poly_act P (gquot X))
  : z = poly_map P (gquot_functor_map (functor_identity X)) z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + abstract
        (intros a₁ a₂ g ;
         apply map_PathOver ;
         refine (whisker_square
                   (idpath _)
                   (!(maponpathsidfun _))
                   (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                   (idpath _)
                   _) ;
         exact (pathscomp0rid _ @ !(pathscomp0lid _))).
    + exact (λ _, gtrunc _ _ _).
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
Defined.

Section LiftPseudofunctor.
  Variable (P : poly_code).

  Definition prealg_gquot_help
             {G₁ G₂ : grpd_bicat}
             (F : grpd_bicat ⟦ G₁, G₂ ⟧)
             {hG₁ : (disp_alg_bicat ⦃ P ⦄) G₁}
             {hG₂ : (disp_alg_bicat ⦃ P ⦄) G₂}
             (hF : hG₁ -->[ F] hG₂)
    : ∏ (z : gquot (poly_act_groupoid P G₁)),
      gquot_functor_map F (gquot_functor_map hG₁ z)
      =
      gquot_functor_map hG₂ (gquot_functor_map (poly_act_functor P G₁ G₂ F) z).
  Proof.
    use gquot_ind_set.
    - exact (λ a, gcleq _ (pr11 hF a)).
    - abstract
      (intros a₁ a₂ g ; simpl ;
      use map_PathOver ;
      refine (whisker_square
                (idpath _)
                _
                _
                (idpath _)
                _)
      ; [refine (!(maponpaths
                    (maponpaths _)
                    (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                    @ _)
              @ maponpathscomp
                  (gquot_functor_map hG₁)
                  (gquot_functor_map F)
                  (gcleq (poly_act_groupoid P G₁) g)) ;
         exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
        | refine (!(maponpaths
                    (maponpaths _)
                    (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                    @ _)
              @ maponpathscomp
                  (gquot_functor_map (poly_act_functor P G₁ G₂ F))
                  (gquot_functor_map hG₂)
                  (gcleq (poly_act_groupoid P G₁) g)) ;
          exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
        | unfold square ;
          refine (!(gconcat _ _ _) @ _ @ gconcat _ _ _) ;
          apply maponpaths ;
          exact (pr21 hF _ _ g)]).
    - exact (λ _, gtrunc _ _ _).
  Defined.

  Definition prealg_gquot_map
             (G : groupoid)
    : (disp_alg_bicat ⦃ P ⦄) G → (disp_alg_bicat (⟦ P ⟧)) (gquot_psfunctor G)
    := λ f x, #gquot_psfunctor f (poly_gquot P G x).

  Definition prealg_gquot_cell
             {G₁ G₂ : grpd_bicat}
             {F : grpd_bicat ⟦ G₁, G₂ ⟧}
             {hG₁ : (disp_alg_bicat ⦃ P ⦄) G₁}
             {hG₂ : (disp_alg_bicat ⦃ P ⦄) G₂}
             (hF : hG₁ -->[ F] hG₂)
             (x : poly_act P (gquot G₁))
    : gquot_functor_map F (gquot_functor_map hG₁ (poly_gquot P G₁ x))
      =
      gquot_functor_map hG₂ (poly_gquot P G₂ (poly_map P (gquot_functor_map F) x)).
  Proof.
    refine (_ @ maponpaths
              (gquot_functor_map hG₂)
              (pr1 (psnaturality_of (poly_gquot P) F) x)).
    exact (prealg_gquot_help F hF (poly_gquot P G₁ x)).
  Defined.

  Definition prealg_gquot_inv_cell
             {G₁ G₂ : grpd_bicat}
             {F : grpd_bicat ⟦ G₁, G₂ ⟧}
             {hG₁ : (disp_alg_bicat ⦃ P ⦄) G₁}
             {hG₂ : (disp_alg_bicat ⦃ P ⦄) G₂}
             (hF : hG₁ -->[ F] hG₂)
    : prealg_gquot_map G₁ hG₁ -->[ # gquot_psfunctor F] prealg_gquot_map G₂ hG₂.
  Proof.
    use make_invertible_2cell.
    - exact (prealg_gquot_cell hF).
    - apply one_type_2cell_iso.
  Defined.

  Definition prealg_gquot_on_cell_help
             {X Y : grpd_bicat}
             {f g : grpd_bicat ⟦ X, Y ⟧}
             {p : f ==> g}
             {hX : (disp_alg_bicat ⦃ P ⦄) X}
             {hY : (disp_alg_bicat ⦃ P ⦄) Y}
             {hf : hX -->[ f] hY}
             {hg : hX -->[ g] hY}
             (hp : hf ==>[ p ] hg)
    : ∏ (z : gquot (poly_act_groupoid P X)),
    prealg_gquot_help f hf z
    @ maponpaths
        (gquot_functor_map hY)
        (gquot_functor_cell (poly_act_nat_trans P X Y f g p) z)
    =
    gquot_functor_cell p (gquot_functor_map hX z)
    @ prealg_gquot_help g hg z.
  Proof.
    use gquot_ind_prop.
    - intro a.
      simpl.
      etrans.
      {
        apply maponpaths.
        exact (gquot_rec_beta_gcleq (poly_act_groupoid P Y) _ _ _ _ _ _ _ _ _).
      }
      refine (!(gconcat _ _ _) @ _ @ gconcat _ _ _).
      apply maponpaths.
      exact (!(nat_trans_eq_pointwise hp a)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.
  
  Definition prealg_gquot_on_cell
             {X Y : grpd_bicat}
             {f g : grpd_bicat ⟦ X, Y ⟧}
             {p : f ==> g}
             {hX : (disp_alg_bicat ⦃ P ⦄) X}
             {hY : (disp_alg_bicat ⦃ P ⦄) Y}
             {hf : hX -->[ f] hY}
             {hg : hX -->[ g] hY}
             (hp : hf ==>[ p ] hg)
             (z : poly_act P (gquot X))
    : gquot_functor_cell p (gquot_functor_map hX ((poly_gquot P) X z))
    @ prealg_gquot_cell hg z
    =
    prealg_gquot_cell hf z
    @ maponpaths
        (λ x, # gquot_psfunctor hY ((poly_gquot P) Y x))
        (poly_homot P (gquot_functor_cell p) z).
  Proof.
    refine (path_assoc _ _ _ @ _ @ path_assoc _ _ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp (poly_gquot P Y) (gquot_functor_map hY) _)).
      }
      refine (!(maponpathscomp0 (gquot_functor_map hY) _ _) @ _).
      etrans.
      {
        apply maponpaths.
        exact (!(eqtohomot (psnaturality_natural (poly_gquot P) _ _ _ _ p) z)).
      }
      apply maponpathscomp0.
    }
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    exact (prealg_gquot_on_cell_help hp (poly_gquot P X z)).
  Qed.
        
  Definition prealg_gquot_identitor_help
             {G : groupoid}
    : ∏ (z : gquot (poly_act_groupoid P G)),
      z
      =
      gquot_functor_map
        (poly_act_functor P _ _ (functor_identity G))
        z.
  Proof.
    intro z.
    refine (gquot_functor_identity _ _ @ _).
    exact (gquot_functor_cell
             (poly_act_functor_identity _ _)
             z).
  Defined.

  Definition prealg_gquot_identitor_lem₁_inl
             {X : groupoid}
             (P₁ P₂ : poly_code)
    : ∏ (z : gquot (poly_act_groupoid P₁ X)),
    maponpaths
      gquot_inl_grpd
      (gquot_functor_identity (poly_act_groupoid P₁ X) z
       @ gquot_functor_cell
           (poly_act_functor_identity P₁ X)
           z)
    =
    (gquot_functor_identity
       (poly_act_groupoid (P₁ + P₂) X)
       (gquot_inl_grpd z)
    @
    gquot_functor_cell
      (poly_act_functor_identity (P₁ + P₂) X)
      (gquot_inl_grpd z))
    @ gquot_inl_grpd_gquot_functor
        (functor_identity X)
        z.
  Proof.
    use gquot_ind_prop.
    - intro q ; simpl.
      etrans.
      {
        exact (gquot_rec_beta_gcleq
                 (poly_act_groupoid P₁ X)
                 _ _ _ _ _ _ _ _
                 (poly_act_functor_identity_data P₁ X q)).
      }
      exact (!(pathscomp0rid _)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.

  Definition prealg_gquot_identitor_lem₁_inr
             {X : groupoid}
             (P₁ P₂ : poly_code)
    : ∏ (z : gquot (poly_act_groupoid P₂ X)),
    maponpaths
      gquot_inr_grpd
      (gquot_functor_identity (poly_act_groupoid P₂ X) z
       @ gquot_functor_cell
           (poly_act_functor_identity P₂ X)
           z)
    =
    (gquot_functor_identity
       (poly_act_groupoid (P₁ + P₂) X)
       (gquot_inr_grpd z)
    @
    gquot_functor_cell
      (poly_act_functor_identity (P₁ + P₂) X)
      (gquot_inr_grpd z))
    @ gquot_inr_grpd_gquot_functor
        (functor_identity X)
        z.
  Proof.
    use gquot_ind_prop.
    - intro q ; simpl.
      etrans.
      {
        exact (gquot_rec_beta_gcleq
                 (poly_act_groupoid P₂ X)
                 _ _ _ _ _ _ _ _
                 (poly_act_functor_identity_data P₂ X q)).
      }
      exact (!(pathscomp0rid _)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.

  Definition prealg_gquot_identitor_lem₁
             (X : groupoid)
             (z : poly_act P (gquot X))
    : maponpaths
        (poly_gquot P X)
        (poly_id P (gquot X) z @ poly_homot P (gquot_functor_identity X) z)
      =
      prealg_gquot_identitor_help
        (poly_gquot P X z)
      @ (pr1 (psnaturality_of (poly_gquot P) (functor_identity X)) z).
  Proof.
    (*
    unfold prealg_gquot_identitor_help.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (!(ge _ _) @ !(pathscomp0rid _)).
    - revert z.
      use gquot_ind_prop.
      + intro a.
        exact (!(ge _ _) @ !(pathscomp0rid _)).
      + intro.
        exact (gtrunc _ _ _ _ _).
    - induction z as [z | z].
      + specialize (IHP₁ z) ; clear IHP₂.
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp0 inl _ _)).
          }
          refine (maponpathscomp _ _ _ @ _).
          refine (!(maponpathscomp _ gquot_inl_grpd _) @ _).
          etrans.
          {
            apply maponpaths.
            exact IHP₁.
          }
          apply maponpathscomp0.
        }
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        exact (prealg_gquot_identitor_lem₁_inl P₁ P₂ _).
      + specialize (IHP₂ z) ; clear IHP₁.
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp0 inr _ _)).
          }
          refine (maponpathscomp _ _ _ @ _).
          refine (!(maponpathscomp _ gquot_inr_grpd _) @ _).
          etrans.
          {
            apply maponpaths.
            exact IHP₂.
          }
          apply maponpathscomp0.
        }
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        exact (prealg_gquot_identitor_lem₁_inr P₁ P₂ _).
    - etrans.
      {
        etrans.
        {
          apply maponpaths.
          exact (pathsdirprod_concat
                   (poly_id P₁ (gquot X) (pr1 z))
                   (poly_homot P₁ (gquot_functor_identity X) (pr1 z))
                   (poly_id P₂ (gquot X) (pr2 z))
                   (poly_homot P₂ (gquot_functor_identity X) (pr2 z))).
        }
        etrans.
        {
          exact (maponpaths_pathsdirprod_precompose
                   prod_gquot_comp
                   (poly_gquot P₁ X)
                   (poly_gquot P₂ X)
                   (poly_id P₁ (gquot X) (pr1 z)
                            @ poly_homot P₁ (gquot_functor_identity X) (pr1 z))
                   (poly_id P₂ (gquot X) (pr2 z)
                            @ poly_homot P₂ (gquot_functor_identity X) (pr2 z))).
        }
        apply maponpaths.
        exact (maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
                @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
      }
     *)
    apply TODO.
    Time Qed.

  Definition prealg_gquot_identitor_lem₂
             {X : grpd_bicat}
             (XX : (disp_alg_bicat ⦃ P ⦄) X)
    : ∏ (z : gquot (poly_act_groupoid P X)),
      maponpaths (gquot_functor_map XX) (prealg_gquot_identitor_help z)
      =
      gquot_functor_identity X (gquot_functor_map XX z)
      @ prealg_gquot_help (id₁ X) (id_disp XX) z.
  Proof.
    use gquot_ind_prop.
    - intro a.
      etrans.
      {
        apply gquot_rec_beta_gcleq.
      }
      simpl.
      apply maponpaths.
      rewrite !id_left.
      apply idpath.
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.

  Definition prealg_gquot
    : disp_psfunctor (disp_alg_bicat ⦃ P ⦄) (disp_alg_bicat (⟦ P ⟧)) gquot_psfunctor.
  Proof.
    use make_disp_psfunctor.
    - apply disp_2cells_isaprop_alg.
    - apply disp_locally_groupoid_alg.
    - exact prealg_gquot_map.
    - exact @prealg_gquot_inv_cell.
    - abstract
        (intros X Y f g p hX hY hf hg hp ;
         use funextsec ;
         intro z ;
         exact (prealg_gquot_on_cell hp z)).
    - intros X XX.
      use funextsec.
      intro z.
      refine (path_assoc _ _ _ @ _).
      refine (maponpaths
                (λ z, z @ _)
                (!(prealg_gquot_identitor_lem₂ XX (poly_gquot P X z)))
              @ _).
      refine (!(maponpathscomp0 (gquot_functor_map XX) _ _) @ _).
      refine (_ @ maponpathscomp0 (prealg_gquot_map X XX) _ _).
      unfold prealg_gquot_map.
      refine (_ @ maponpathscomp _ (gquot_functor_map XX) _).
      apply maponpaths.
      apply TODO.
    - intros X Y Z f g hX hY hZ hf hg.
      use funextsec.
      intro z.
      (*
      simpl.
      cbn.
      unfold homotcomp, homotfun, funhomotsec.
      simpl.
      cbn.
      unfold gquot_functor_composition.
      unfold prealg_gquot_cell.
       *)
      apply TODO.
  Defined.
End LiftPseudofunctor.
