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

Definition prealg_gquot_help
           (P : poly_code)
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
           (P : poly_code)
           (G : groupoid)
  : (disp_alg_bicat ⦃ P ⦄) G → (disp_alg_bicat (⟦ P ⟧)) (gquot_psfunctor G)
  := λ f x, #gquot_psfunctor f (poly_gquot P G x).

Definition prealg_gquot_cell
           (P : poly_code)
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
  exact (prealg_gquot_help P F hF (poly_gquot P G₁ x)).
Defined.

Definition prealg_gquot_inv_cell
           (P : poly_code)
           {G₁ G₂ : grpd_bicat}
           {F : grpd_bicat ⟦ G₁, G₂ ⟧}
           {hG₁ : (disp_alg_bicat ⦃ P ⦄) G₁}
           {hG₂ : (disp_alg_bicat ⦃ P ⦄) G₂}
           (hF : hG₁ -->[ F] hG₂)
  : prealg_gquot_map P G₁ hG₁ -->[ # gquot_psfunctor F] prealg_gquot_map P G₂ hG₂.
Proof.
  use make_invertible_2cell.
  - exact (prealg_gquot_cell P hF).
  - apply one_type_2cell_iso.
Defined.

Definition prealg_gquot_on_cell_help
           (P : poly_code)
           {X Y : grpd_bicat}
           {f g : grpd_bicat ⟦ X, Y ⟧}
           {p : f ==> g}
           {hX : (disp_alg_bicat ⦃ P ⦄) X}
           {hY : (disp_alg_bicat ⦃ P ⦄) Y}
           {hf : hX -->[ f] hY}
           {hg : hX -->[ g] hY}
           (hp : hf ==>[ p ] hg)
  : ∏ (z : gquot (poly_act_groupoid P X)),
    prealg_gquot_help P f hf z
    @ maponpaths
        (gquot_functor_map hY)
        (gquot_functor_cell (poly_act_nat_trans P X Y f g p) z)
    =
    gquot_functor_cell p (gquot_functor_map hX z)
    @ prealg_gquot_help P g hg z.
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
           (P : poly_code)
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
                       @ prealg_gquot_cell P hg z
    =
    prealg_gquot_cell P hf z
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
  exact (prealg_gquot_on_cell_help P hp (poly_gquot P X z)).
Qed.

Definition prealg_gquot_identitor_help
           (P : poly_code)
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

Local Definition psnaturality_pg
      {P : poly_code}
      {X Y : grpd_bicat}
      (f : grpd_bicat ⟦ X, Y ⟧)
      (z : poly_act P (gquot X))
  : gquot_functor_map
      (poly_act_functor P X Y f)
      (poly_gquot P X z)
    =
    (poly_gquot P) Y (poly_map P (gquot_functor_map f) z)
  := pr1 (psnaturality_of (poly_gquot P) f) z.

Definition prealg_gquot_identitor_lem₁
           (P : poly_code)
           (X : groupoid)
           (z : poly_act P (gquot X))
  : maponpaths
      (poly_gquot P X)
      (poly_id P (gquot X) z @ poly_homot P (gquot_functor_identity X) z)
    =
    prealg_gquot_identitor_help
      P
      (poly_gquot P X z)
    @ psnaturality_pg (functor_identity X) z.
Proof.
  pose (eqtohomot (pstrans_id (poly_gquot P) X) z) as p.
  simpl in p. cbn in p.
  unfold homotcomp, funhomotsec, homotfun in p.
  cbn in p.
  unfold prealg_gquot_identitor_help.
  exact (!p).
Qed.

Definition prealg_gquot_identitor_lem₂
           (P : poly_code)
           {X : grpd_bicat}
           (XX : (disp_alg_bicat ⦃ P ⦄) X)
  : ∏ (z : gquot (poly_act_groupoid P X)),
    maponpaths (gquot_functor_map XX) (prealg_gquot_identitor_help P z)
    =
    gquot_functor_identity X (gquot_functor_map XX z)
                           @ prealg_gquot_help P (id₁ X) (id_disp XX) z.
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

Definition poly_act_morphism_poly_map_comp
           {P : poly_code}
           {X Y Z : grpd_bicat}
           (f : grpd_bicat ⟦ X, Y ⟧)
           (g : grpd_bicat ⟦ Y, Z ⟧)
           (z : poly_act P (X : groupoid))
  : poly_act_morphism
      P Z
      (poly_map P (pr1 g) (poly_map P (pr1 f) z))
      (poly_map P (λ a, pr1 g (pr1 f a)) z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply identity.
  - induction z as [z | z].
    + exact (IHP₁ z).
    + exact (IHP₂ z).
  - exact (IHP₁ (pr1 z) ,, IHP₂ (pr2 z)).
Defined.

Definition gquot_functor_map_poly_act_poly_gquot_help
           {P : poly_code}
           {X Y Z : grpd_bicat}
           (f : grpd_bicat ⟦ X, Y ⟧)
           (g : grpd_bicat ⟦ Y, Z ⟧)
  : ∏ (z : gquot (poly_act_groupoid P X)),
    gquot_functor_map
      (poly_act_functor P Y Z g)
      (gquot_functor_map
         (poly_act_functor P X Y f)
         z)
    =
    gquot_functor_map
      (poly_act_functor P X Z (f ∙ g))
      z
  := λ z, gquot_functor_composition
            (poly_act_functor P X Y f) (poly_act_functor P Y Z g)
            z
         @ gquot_functor_cell (poly_act_functor_composition P X Y Z f g) z.

Definition gquot_functor_map_poly_act_poly_gquot
           {P : poly_code}
           {X Y Z : grpd_bicat}
           (f : grpd_bicat ⟦ X, Y ⟧)
           (g : grpd_bicat ⟦ Y, Z ⟧)
           (z : poly_act P (gquot X))
  : gquot_functor_map
      (poly_act_functor P Y Z g)
      (poly_gquot P Y (poly_map P (gquot_functor_map f) z))
    =
    gquot_functor_map
      (poly_act_functor P X Z (f ∙ g))
      (poly_gquot P X z)
  := maponpaths
       (gquot_functor_map
          (poly_act_functor P Y Z g))
       (!pr1 (psnaturality_of (poly_gquot P) f) z)
     @ gquot_functor_map_poly_act_poly_gquot_help f g (poly_gquot P X z).

Definition prealg_gquot_compositor_lem₁
           {P : poly_code}
           {X Y Z : grpd_bicat}
           {f : grpd_bicat ⟦ X, Y ⟧}
           {g : grpd_bicat ⟦ Y, Z ⟧}
           {hX : (disp_alg_bicat ⦃ P ⦄) X}
           {hY : (disp_alg_bicat ⦃ P ⦄) Y}
           {hZ : (disp_alg_bicat ⦃ P ⦄) Z}
           (hf : hX -->[ f] hY)
           (hg : hY -->[ g] hZ)
           (z : poly_act P (gquot X))
           (q : hX ∙ (f ∙ g) ⟹ poly_act_functor P X Z (f ∙ g) ∙ hZ)
           (Hq : @is_invertible_2cell grpd_bicat _ _ _ _ q)
           (qa : ∏ (a : poly_act P (X : groupoid)),
                 # (g : _ ⟶ _) ((pr11 hf) a)
                   · ((pr11 hg) (poly_map P (f : _ ⟶ _) a)
                   · # (pr1 hZ) (poly_act_morphism_poly_map_comp f g a))
                 = 
                 pr1 q a)
  : gquot_functor_composition f g (gquot_functor_map hX ((poly_gquot P) X z))
  @ prealg_gquot_help P (f ∙ g) (q ,, Hq) ((poly_gquot P) X z)
  =
  maponpaths
    (gquot_functor_map g)
    (prealg_gquot_help P f hf ((poly_gquot P) X z)
     @ maponpaths
         (gquot_functor_map hY)
         (psnaturality_pg f z))
  @ prealg_gquot_help
      P g hg
      ((poly_gquot P) Y (poly_map P (gquot_functor_map f) z))
  @ maponpaths
      (gquot_functor_map hZ)
      (gquot_functor_map_poly_act_poly_gquot f g z).
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    exact (maponpathscomp0 (gquot_functor_map g) _ _).
  }
  etrans.
  {
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp.
    }
    pose (homotsec_natural'
            (prealg_gquot_help P g hg)
            (psnaturality_pg f z))
      as h.
    simpl in h.
    cbn in h.
    exact h.
  }
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply maponpaths.
    exact (!(maponpathscomp _ _ _)).
  }      
  etrans.
  {
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!(maponpathscomp0 _ _ _) @ _).
    apply maponpaths.
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (!(maponpathscomp0 _ _ _) @ _).
      apply maponpaths.
      exact (pathsinv0r _).
    }
    apply pathscomp0lid.
  }
  generalize (poly_gquot P X z).
  use gquot_ind_prop.
  - intro a.
    simpl.
    etrans.
    {
      apply maponpaths_2.
      exact (gquot_rec_beta_gcleq Y _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      do 2 apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      apply maponpaths.
      exact (!(gconcat _ _ _)).
    }
    refine (!(gconcat _ _ _) @ _).
    apply maponpaths.
    exact (qa a).
  - exact (λ _, gtrunc _ _ _ _ _).
Qed.

Local Definition pstrans_comp_pg
      {P : poly_code}
      {X Y Z : grpd_bicat}
      (f : grpd_bicat ⟦ X, Y ⟧)
      (g : grpd_bicat ⟦ Y, Z ⟧)
      (z : poly_act P (gquot X))
  : (gquot_functor_composition
       (poly_act_functor P X Y f)
       (poly_act_functor P Y Z g)
       (poly_gquot P X z)
  @ gquot_functor_cell
      (poly_act_functor_composition P X Y Z f g)
      ((poly_gquot P) X z))
  @ psnaturality_pg (f ∙ g) z
  =
  (((maponpaths
       (gquot_functor_map (poly_act_functor P Y Z g))
       (psnaturality_pg f z)
  @ idpath _)
  @ (psnaturality_pg g (poly_map P (gquot_functor_map f) z)))
  @ idpath _)
  @ maponpaths
      (poly_gquot P Z)
      (poly_comp P (gquot_functor_map f) (gquot_functor_map g) z
  @ poly_homot P (gquot_functor_composition f g) z).
Proof.
  unfold psnaturality_pg.
  pose (eqtohomot (pstrans_comp (poly_gquot P) f g) z).
  simpl in p.
  exact p.
Qed.
  
Definition prealg_gquot_compositor_lem₂
           {P : poly_code}
           {X Y Z : grpd_bicat}
           (f : grpd_bicat ⟦ X, Y ⟧)
           (g : grpd_bicat ⟦ Y, Z ⟧)
           (z : poly_act P (gquot X))
  : psnaturality_pg g (poly_map P (gquot_functor_map f) z)
  @ maponpaths
      (poly_gquot P Z)
      (poly_comp P (gquot_functor_map f) (gquot_functor_map g) z
       @ poly_homot P (gquot_functor_composition f g) z)
  =
  gquot_functor_map_poly_act_poly_gquot f g z @ psnaturality_pg (f ∙ g) z.
Proof.
  refine (!_).
  refine (!(path_assoc _ _ _) @ _).
  etrans.
  {
    apply maponpaths.
    exact (pstrans_comp_pg f g z).
  }
  rewrite !pathscomp0rid.
  refine (path_assoc _ _ _ @ _).
  apply maponpaths_2.
  refine (path_assoc _ _ _ @ _).
  etrans.
  {
    apply maponpaths_2.
    refine (!(maponpathscomp0 _ _ _) @ _).
    apply maponpaths.
    apply pathsinv0l.
  }
  apply idpath.
Qed.

Definition prealg_gquot_compositor
           {P : poly_code}
           {X Y Z : grpd_bicat}
           {f : grpd_bicat ⟦ X, Y ⟧}
           {g : grpd_bicat ⟦ Y, Z ⟧}
           {hX : (disp_alg_bicat ⦃ P ⦄) X}
           {hY : (disp_alg_bicat ⦃ P ⦄) Y}
           {hZ : (disp_alg_bicat ⦃ P ⦄) Z}
           (hf : hX -->[ f] hY)
           (hg : hY -->[ g] hZ)
           (z : poly_act P (gquot X))
           (q : hX ∙ (f ∙ g) ⟹ poly_act_functor P X Z (f ∙ g) ∙ hZ)
           (Hq : @is_invertible_2cell grpd_bicat _ _ _ _ q)
           (qa : ∏ (a : poly_act P (X : groupoid)),
                 # (g : _ ⟶ _) ((pr11 hf) a)
                   · ((pr11 hg) (poly_map P (f : _ ⟶ _) a)
                   · # (pr1 hZ) (poly_act_morphism_poly_map_comp f g a))
                 = 
                 pr1 q a)
  : gquot_functor_composition
      f g
      (gquot_functor_map hX (poly_gquot P X z))
  @ prealg_gquot_help
      P (f ∙ g) (q ,, Hq)
      (poly_gquot P X z)
  @ maponpaths
      (gquot_functor_map hZ)
      (psnaturality_pg (f ∙ g) z)
  =
  ((maponpaths
      (gquot_functor_map g)
      (prealg_gquot_help P f hf (poly_gquot P X z)
       @
       maponpaths
         (gquot_functor_map hY)
         (psnaturality_pg f z))
  @ prealg_gquot_help
      P g hg
      (poly_gquot P Y (poly_map P (gquot_functor_map f) z))
  @ maponpaths
      (gquot_functor_map hZ)
      (psnaturality_pg g (poly_map P (gquot_functor_map f) z)))
  @ maponpaths
      (prealg_gquot_map P Z hZ)
      (poly_comp P (gquot_functor_map f) (gquot_functor_map g) z))
  @ maponpaths
      (prealg_gquot_map P Z hZ)
      (poly_homot P (gquot_functor_composition f g) z).
Proof.
  etrans.
  {
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    exact (prealg_gquot_compositor_lem₁ hf hg z q Hq qa).
  }
  refine (!(path_assoc _ _ _) @ _).
  do 2 refine (_ @ path_assoc _ _ _).
  apply maponpaths.
  refine (!(path_assoc _ _ _) @ _).
  refine (_ @ path_assoc _ _ _).
  apply maponpaths.
  refine (!(maponpathscomp0 _ _ _) @ _).
  refine (!_).
  etrans.
  {
    etrans.
    {
      apply maponpaths.
      refine (!(maponpathscomp0 (prealg_gquot_map P Z hZ) _ _) @ _).
      exact (!(maponpathscomp (poly_gquot P Z) (gquot_functor_map hZ) _)).
    }
    exact (!(maponpathscomp0 _ _ _)).
  }
  apply maponpaths.
  apply prealg_gquot_compositor_lem₂.
Qed.

Definition prealg_gquot
           (P : poly_code)
  : disp_psfunctor (disp_alg_bicat ⦃ P ⦄) (disp_alg_bicat (⟦ P ⟧)) gquot_psfunctor.
Proof.
  use make_disp_psfunctor.
  - apply disp_2cells_isaprop_alg.
  - apply disp_locally_groupoid_alg.
  - exact (prealg_gquot_map P).
  - exact (@prealg_gquot_inv_cell P).
  - abstract
      (intros X Y f g p hX hY hf hg hp ;
       use funextsec ;
       intro z ;
       exact (prealg_gquot_on_cell P hp z)).
  - abstract
      (intros X XX ;
       use funextsec ;
       intro z ;
       refine (path_assoc _ _ _ @ _) ;
       refine (maponpaths
                 (λ z, z @ _)
                 (!(prealg_gquot_identitor_lem₂ P XX (poly_gquot P X z)))
                 @ _) ;
       refine (!(maponpathscomp0 (gquot_functor_map XX) _ _) @ _) ;
       refine (_ @ maponpathscomp0 (prealg_gquot_map P X XX) _ _) ;
       unfold prealg_gquot_map ;
       refine (_ @ maponpathscomp _ (gquot_functor_map XX) _) ;
       apply maponpaths ;
       exact (!(prealg_gquot_identitor_lem₁ P X _))).
  - abstract
      (intros X Y Z f g hX hY hZ hf hg ;
       use funextsec ;
       intro z ;
       refine (!_) ;
       refine (maponpaths
                 (λ z, (z @ _) @ _)
                 (pathscomp0rid _
                   @ maponpaths
                       (λ z, z @ _)
                       (pathscomp0rid _))
                 @ _) ;
       refine (!_) ;
       apply (prealg_gquot_compositor hf hg z) ;
       intros a ;
       refine (!_) ;
       refine (maponpaths
                 (λ z, z · _)
                 (id_right _
                  @ maponpaths
                      (λ z, z · _)
                      (id_right _ @ id_left _))
                 @ _) ;
       refine (!_) ;
       apply assoc).
Defined.
