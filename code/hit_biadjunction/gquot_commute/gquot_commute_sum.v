(** Commutation of groupoid quotient with sums *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

Opaque ps_comp.

Definition gquot_inl_grpd
           {P₁ P₂ : poly_code}
           {G : groupoid}
  : gquot (poly_act_groupoid P₁ G) → gquot (poly_act_groupoid (P₁ + P₂) G).
Proof.
  use gquot_rec.
  - exact (λ z, gcl (poly_act_groupoid (P₁ + P₂) G) (inl z)).
  - exact (λ a₁ a₂ g, @gcleq (poly_act_groupoid (P₁ + P₂) G) (inl a₁) (inl a₂) g).
  - exact (λ _, ge _ _).
  - exact (λ a₁ a₂ a₃ g₁ g₂,
           @gconcat
             (poly_act_groupoid (P₁ + P₂) G)
             (inl a₁) (inl a₂) (inl a₃) g₁ g₂).
  - apply gtrunc.
Defined.

Definition gquot_inr_grpd
           {P₁ P₂ : poly_code}
           {G : groupoid}
  : gquot (poly_act_groupoid P₂ G) → gquot (poly_act_groupoid (P₁ + P₂) G).
Proof.
  use gquot_rec.
  - exact (λ z, gcl (poly_act_groupoid (P₁ + P₂) G) (inr z)).
  - exact (λ a₁ a₂ g, @gcleq (poly_act_groupoid (P₁ + P₂) G) (inr a₁) (inr a₂) g).
  - exact (λ _, ge _ _).
  - exact (λ a₁ a₂ a₃ g₁ g₂,
           @gconcat
             (poly_act_groupoid (P₁ + P₂) G)
             (inr a₁) (inr a₂) (inr a₃) g₁ g₂).
  - apply gtrunc.
Defined.

Section GQuotSum.
  Context {P₁ P₂ : poly_code}
          (IHP₁ : pstrans
                    (ps_comp (⟦ P₁ ⟧) gquot_psfunctor)
                    (ps_comp gquot_psfunctor ⦃ P₁ ⦄))
          (IHP₂ : pstrans
                    (ps_comp (⟦ P₂ ⟧) gquot_psfunctor)
                    (ps_comp gquot_psfunctor ⦃ P₂ ⦄)).

  Definition sum_gquot_data_comp
             (X : grpd_bicat)
    : (ps_comp (⟦ P₁ + P₂ ⟧) gquot_psfunctor) X
      -->
      (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄) X.
  Proof.
    intro z.
    induction z as [z | z].
    - exact (gquot_inl_grpd (IHP₁ X z)).
    - exact (gquot_inr_grpd (IHP₂ X z)).
  Defined.
  
  Definition gquot_inl_grpd_gquot_functor
             {X Y : grpd_bicat}
             (f : X --> Y)
    : ∏ (z : gquot (⦃ P₁ ⦄ X)),
      # (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄) f (gquot_inl_grpd z)
      =
      gquot_inl_grpd (gquot_functor_map (# ⦃ P₁ ⦄ f) z).
  Proof.
    use gquot_ind_set.
    - exact (λ _, idpath _).
    - abstract
        (intros a₁ a₂ g ;
         use map_PathOver ;
         refine (whisker_square
                   (idpath _)
                   _
                   _
                   (idpath _)
                   _) ;
           [ refine (!(!(maponpathscomp _ _ _) @ _)) ;
             refine (maponpaths
                       (maponpaths (gquot_functor_map (poly_act_functor (P₁ + P₂) X Y f)))
                       (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _) @ _) ;
             apply gquot_rec_beta_gcleq
           | refine (!(!(maponpathscomp _ _ _) @ _)) ;
             refine (maponpaths
                       (maponpaths gquot_inl_grpd)
                       (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _) @ _) ;
             apply gquot_rec_beta_gcleq
           | apply vrefl]).
    - intro.
      exact (gtrunc _ _ _).
  Defined.

  Definition sum_gquot_data_nat_inl
             {X Y : grpd_bicat}
             (f : X --> Y)
             (z : ⟦ P₁ ⟧ (gquot_psfunctor X) : one_type)
    : # (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄) f (gquot_inl_grpd (IHP₁ X z))
      =
      sum_gquot_data_comp Y (inl (# (⟦ P₁ ⟧) (gquot_functor_map f) z)).
  Proof.
    refine (_ @ maponpaths gquot_inl_grpd (pr1 (psnaturality_of IHP₁ f) z)).
    exact (gquot_inl_grpd_gquot_functor f (IHP₁ X z)).
  Defined.

  Definition gquot_inr_grpd_gquot_functor
             {X Y : grpd_bicat}
             (f : X --> Y)
    : ∏ (z : gquot (⦃ P₂ ⦄ X)),
      # (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄) f (gquot_inr_grpd z)
      =
      gquot_inr_grpd (gquot_functor_map (# ⦃ P₂ ⦄ f) z).
  Proof.
    use gquot_ind_set.
    - exact (λ _, idpath _).
    - abstract
        (intros a₁ a₂ g ;
         use map_PathOver ;
         refine (whisker_square
                   (idpath _)
                   _
                   _
                   (idpath _)
                   _) ;
           [ refine (!(!(maponpathscomp _ _ _) @ _)) ;
             refine (maponpaths
                       (maponpaths (gquot_functor_map (poly_act_functor (P₁ + P₂) X Y f)))
                       (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _) @ _) ;
             apply gquot_rec_beta_gcleq
           | refine (!(!(maponpathscomp _ _ _) @ _)) ;
             refine (maponpaths
                       (maponpaths gquot_inr_grpd)
                       (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _) @ _) ;
             apply gquot_rec_beta_gcleq
           | apply vrefl]).
    - intro.
      exact (gtrunc _ _ _).
  Defined.

  Definition sum_gquot_data_nat_inr
             {X Y : grpd_bicat}
             (f : X --> Y)
             (z : ⟦ P₂ ⟧ (gquot_psfunctor X) : one_type)
    : # (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄) f (gquot_inr_grpd (IHP₂ X z))
      =
      sum_gquot_data_comp Y (inr (# (⟦ P₂ ⟧) (gquot_functor_map f) z)).
  Proof.
    refine (_ @ maponpaths gquot_inr_grpd (pr1 (psnaturality_of IHP₂ f) z)).
    exact (gquot_inr_grpd_gquot_functor f (IHP₂ X z)).
  Defined.

  Definition sum_gquot_data
    : pstrans_data
        (ps_comp (⟦ P₁ + P₂ ⟧) gquot_psfunctor)
        (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄).
  Proof.
    use make_pstrans_data.
    - exact sum_gquot_data_comp.
    - intros X Y f.
      use make_invertible_2cell.
      + intro z.
        induction z as [z | z].
        * exact (sum_gquot_data_nat_inl f z).
        * exact (sum_gquot_data_nat_inr f z).
      + apply one_type_2cell_iso.
  Defined.
  
  Definition sum_gquot_naturality_help_inl
             {X Y : grpd_bicat}
             {f g : grpd_bicat ⟦ X, Y ⟧}
             (p : f ==> g)
    : ∏ (z : gquot (⦃ P₁ ⦄ X)),
      (gquot_inl_grpd_gquot_functor f z)
        @ maponpaths
            gquot_inl_grpd
            (gquot_functor_cell
               (poly_act_nat_trans P₁ X Y f g p) z)
      =
      (gquot_functor_cell
        (poly_act_nat_trans (P₁ + P₂) X Y f g p) (gquot_inl_grpd z))
      @ gquot_inl_grpd_gquot_functor g z.
  Proof.
    use gquot_ind_prop.
    - intro a.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      refine (!_).
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ (pr1 (## ⦃ P₁ ⦄ p) a)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.
  
  Definition sum_gquot_naturality_help_inr
             {X Y : grpd_bicat}
             {f g : grpd_bicat ⟦ X, Y ⟧}
             (p : f ==> g)
    : ∏ (z : gquot (⦃ P₂ ⦄ X)),
      (gquot_inr_grpd_gquot_functor f z)
        @ maponpaths gquot_inr_grpd
            (gquot_functor_cell
               (poly_act_nat_trans P₂ X Y f g p) z)
      =
      gquot_functor_cell
        (poly_act_nat_trans (P₁ + P₂) X Y f g p) (gquot_inr_grpd z)
      @ gquot_inr_grpd_gquot_functor g z.
    Proof.
    use gquot_ind_prop.
    - intro a.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      refine (!_).
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ (pr1 (## ⦃ P₂ ⦄ p) a)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.

  Definition sum_gquot_id_help_inl
             {X : grpd_bicat}
    : ∏ z,
      maponpaths
        gquot_inl_grpd
        ((pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₁ ⦄))) X z)
      =
      (pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄)))
        X (gquot_inl_grpd z)
        @ gquot_inl_grpd_gquot_functor (id₁ X) z.
  Proof.
    use gquot_ind_prop.
    - intro a.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      refine (!_).
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ (pr1 (pr122 (pr1 ⦃ P₁⦄) X) a)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.

  Definition sum_gquot_id_help_inr
             {X : grpd_bicat}
    : ∏ z,
      maponpaths
        gquot_inr_grpd
        ((pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₂ ⦄))) X z)
      =
      (pr122 (pr1 (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄)))
        X (gquot_inr_grpd z)
        @ gquot_inr_grpd_gquot_functor (id₁ X) z.
  Proof.
    use gquot_ind_prop.
    - intro a.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      refine (!_).
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ (pr1 (pr122 (pr1 ⦃ P₂ ⦄) X) a)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.
  
  Definition sum_gquot_pstrans_comp_inl_help
             {X Y Z : grpd_bicat}
             (f : X --> Y) (g : Y --> Z)
             {x y : gquot (⦃ P₁ ⦄ Y)}
             (p : x = y)             
    : maponpaths
        (gquot_functor_map (# ⦃ P₁ + P₂ ⦄ g))
        (maponpaths gquot_inl_grpd p)
        @ gquot_inl_grpd_gquot_functor
            g y
      =
      (gquot_inl_grpd_gquot_functor _ _)
        @ maponpaths
        gquot_inl_grpd
        (maponpaths
           (gquot_functor_map (# ⦃ P₁ ⦄ g))
           p).
  Proof.
    induction p.
    refine (!_).
    apply pathscomp0rid.
  Qed.
  
  Definition sum_gquot_pstrans_comp_inl_help_two
             {X Y Z : grpd_bicat}
             (f : X --> Y) (g : Y --> Z)
    : ∏ (z : gquot (⦃ P₁ ⦄ X)),
      maponpaths
        (gquot_functor_map (poly_act_functor (P₁ + P₂) Y Z g))
        (gquot_inl_grpd_gquot_functor f z)
    @ gquot_inl_grpd_gquot_functor
        g
        (gquot_functor_map (poly_act_functor P₁ X Y f) z)
    @ maponpaths
        gquot_inl_grpd
        (gquot_functor_composition
           (poly_act_functor P₁ X Y f)
           (poly_act_functor P₁ Y Z g)
           z
    @ gquot_functor_cell
           (poly_act_functor_composition P₁ X Y Z f g) 
           z)
    =
      (gquot_functor_composition
         (poly_act_functor (P₁ + P₂) X Y f)
         (poly_act_functor (P₁ + P₂) Y Z g)
         (gquot_inl_grpd z)
    @ gquot_functor_cell
        (poly_act_functor_composition (P₁ + P₂) X Y Z f g)
        (gquot_inl_grpd z))
    @ gquot_inl_grpd_gquot_functor (f ∙ g) z.
  Proof.
    use gquot_ind_prop.
    - intro a.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      refine (!_).
      exact (gquot_rec_beta_gcleq
                _ _ _ _ _ _ _ _ _
                (pr1 ((pr222 (pr1 ⦃ P₁ ⦄)) X Y Z f g) a)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.

  Definition sum_gquot_pstrans_comp_inr_help
             {X Y Z : grpd_bicat}
             (f : X --> Y) (g : Y --> Z)
             {x y : gquot (⦃ P₂ ⦄ Y)}
             (p : x = y)             
    : maponpaths
        (gquot_functor_map (# ⦃ P₁ + P₂ ⦄ g))
        (maponpaths gquot_inr_grpd p)
        @ gquot_inr_grpd_gquot_functor
        g y
      =
      (gquot_inr_grpd_gquot_functor _ _)
        @ maponpaths
        gquot_inr_grpd
        (maponpaths
           (gquot_functor_map (# ⦃ P₂ ⦄ g))
           p).
  Proof.
    induction p.
    refine (!_).
    apply pathscomp0rid.
  Qed.

  Definition sum_gquot_pstrans_comp_inr_help_two
             {X Y Z : grpd_bicat}
             (f : X --> Y) (g : Y --> Z)
    : ∏ (z : gquot (⦃ P₂ ⦄ X)),
      maponpaths
        (gquot_functor_map (poly_act_functor (P₁ + P₂) Y Z g))
        (gquot_inr_grpd_gquot_functor f z)
    @ gquot_inr_grpd_gquot_functor
        g
        (gquot_functor_map (poly_act_functor P₂ X Y f) z)
    @ maponpaths
        gquot_inr_grpd
        (gquot_functor_composition
           (poly_act_functor P₂ X Y f)
           (poly_act_functor P₂ Y Z g)
           z
    @ gquot_functor_cell
           (poly_act_functor_composition P₂ X Y Z f g) 
           z)
    =
      (gquot_functor_composition
         (poly_act_functor (P₁ + P₂) X Y f)
         (poly_act_functor (P₁ + P₂) Y Z g)
         (gquot_inr_grpd z)
    @ gquot_functor_cell
        (poly_act_functor_composition (P₁ + P₂) X Y Z f g)
        (gquot_inr_grpd z))
    @ gquot_inr_grpd_gquot_functor (f ∙ g) z.
  Proof.
    use gquot_ind_prop.
    - intro a.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      refine (!_).
      exact (gquot_rec_beta_gcleq
                _ _ _ _ _ _ _ _ _
                (pr1 ((pr222 (pr1 ⦃ P₂ ⦄)) X Y Z f g) a)).
    - intro.
      exact (gtrunc _ _ _ _ _).
  Qed.

  Definition sum_gquot_is_pstrans
    : is_pstrans sum_gquot_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      intro z.
      induction z as [z | z].
      + refine (!_).
        etrans.
        {
          etrans.
          {
            refine (maponpaths (λ z, _ @ z) _).
            refine (maponpathscomp inl (sum_gquot_data_comp Y) _  @ _).
            exact (!(maponpathscomp (IHP₁ Y) gquot_inl_grpd _)).
          }
          refine (!(path_assoc _ _ _) @ _).
          refine (maponpaths (λ z, _ @ z) _).
          refine (!(maponpathscomp0 _ _ _) @ _).
          refine (maponpaths
                   (maponpaths gquot_inl_grpd)
                   (!(eqtohomot (psnaturality_natural IHP₁ X Y f g p) z)) @ _).
          exact (maponpathscomp0 _ _ _).
        }
        refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
        refine (maponpaths (λ z, z @ _) _).
        exact (sum_gquot_naturality_help_inl p (IHP₁ X z)).
      + refine (!_).
        etrans.
        {
          etrans.
          {
            refine (maponpaths (λ z, _ @ z) _).
            refine (maponpathscomp inr (sum_gquot_data_comp Y) _  @ _).
            exact (!(maponpathscomp (IHP₂ Y) gquot_inr_grpd _)).
          }
          refine (!(path_assoc _ _ _) @ _).
          refine (maponpaths (λ z, _ @ z) _).
          refine (!(maponpathscomp0 _ _ _) @ _).
          refine (maponpaths
                    (maponpaths gquot_inr_grpd)
                    (!(eqtohomot (psnaturality_natural IHP₂ X Y f g p) z)) @ _).
          exact (maponpathscomp0 _ _ _).
        }
        refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
        refine (maponpaths (λ z, z @ _) _).
        exact (sum_gquot_naturality_help_inr p (IHP₂ X z)).
    - intros X.
      use funextsec.
      intro z.
      induction z as [z | z].
      + refine (!_).
        etrans.
        {
          refine (maponpathscomp0 (sum_gquot_data_comp X) _ _ @ _).
          etrans.
          {
            refine (maponpaths (λ z, z @ _) _).
            refine (maponpathscomp inl (sum_gquot_data_comp X) _  @ _).
            exact (!(maponpathscomp (IHP₁ X) gquot_inl_grpd _)).
          }
          etrans.
          {
            refine (maponpaths (λ z, _ @ z) _).
            refine (maponpathscomp inl (sum_gquot_data_comp X) _  @ _).
            exact (!(maponpathscomp (IHP₁ X) gquot_inl_grpd _)).
          }
          refine (!(maponpathscomp0 gquot_inl_grpd _ _) @ _).
          refine (maponpaths (maponpaths gquot_inl_grpd) _).
          refine (!(maponpathscomp0 (IHP₁ X) _ _) @ _).
          exact (!(eqtohomot (pstrans_id IHP₁ X) z)).
        }
        refine (maponpathscomp0 gquot_inl_grpd _ _ @ _).
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        apply sum_gquot_id_help_inl.
      + refine (!_).
        etrans.
        {
          refine (maponpathscomp0 (sum_gquot_data_comp X) _ _ @ _).
          etrans.
          {
            refine (maponpaths (λ z, z @ _) _).
            refine (maponpathscomp inr (sum_gquot_data_comp X) _  @ _).
            exact (!(maponpathscomp (IHP₂ X) gquot_inr_grpd _)).
          }
          etrans.
          {
            refine (maponpaths (λ z, _ @ z) _).
            refine (maponpathscomp inr (sum_gquot_data_comp X) _  @ _).
            exact (!(maponpathscomp (IHP₂ X) gquot_inr_grpd _)).
          }
          refine (!(maponpathscomp0 gquot_inr_grpd _ _) @ _).
          refine (maponpaths (maponpaths gquot_inr_grpd) _).
          refine (!(maponpathscomp0 (IHP₂ X) _ _) @ _).
          exact (!(eqtohomot (pstrans_id IHP₂ X) z)).
        }
        refine (maponpathscomp0 gquot_inr_grpd _ _ @ _).
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        apply sum_gquot_id_help_inr.
    - intros X Y Z f g.
      use funextsec.
      intro z.
      induction z as [z | z].
      + refine (!_).
        etrans.
        {
          refine (maponpaths (λ z, z @ _) (_ @ _)).
          { apply pathscomp0rid. }
          refine (maponpaths (λ z, z @ _) _).
          apply pathscomp0rid.
        }
        etrans.
        {
          refine (maponpaths (λ z, _ @ z) _).
          refine (maponpathscomp0 (sum_gquot_data_comp Z) _ _ @ _).
          etrans.
          {
            refine (maponpaths (λ z, z @ _) _).
            refine (maponpathscomp inl (sum_gquot_data_comp Z) _  @ _).
            exact (!(maponpathscomp (IHP₁ Z) gquot_inl_grpd _)).
          }
          etrans.
          {
            refine (maponpaths (λ z,
                                maponpaths
                                  gquot_inl_grpd
                                  (maponpaths
                                     (IHP₁ Z)
                                     _
                                  )
                                  @ z) _).
            refine (maponpathscomp inl (sum_gquot_data_comp Z) _  @ _).
            exact (!(maponpathscomp (IHP₁ Z) gquot_inl_grpd _)).
          }
          refine (!(maponpathscomp0 gquot_inl_grpd _ _) @ _).
          refine (maponpaths (maponpaths gquot_inl_grpd) _).
          exact (!(maponpathscomp0 (IHP₁ Z) _ _)).
        }
        etrans.
        {
          refine (maponpaths (λ z, (z @ _) @ _) _).
          exact ((maponpathscomp0 (gquot_functor_map _) _ _)).
        }
        do 2 (refine (!(path_assoc _ _ _) @ _)).
        etrans.
        {
          refine (maponpaths (λ z, _ @ z) _).
          etrans.
          {
            refine (maponpaths (λ z, _ @ z) _).
            refine (!(path_assoc _ _ _) @ _).
            refine (maponpaths (λ z, _ @ z) _).
            exact (!(maponpathscomp0 gquot_inl_grpd _ _)).
          }
          refine (path_assoc _ _ _ @ _).
          refine (maponpaths (λ z, z @ _) _).
          exact (sum_gquot_pstrans_comp_inl_help f g ((pr1 (psnaturality_of IHP₁ f)) z)).
        }
        etrans.
        {
          refine (maponpaths (λ z, _ @ z) _).
          refine (!(path_assoc _ _ _) @ _).
          refine (maponpaths (λ z, _ @ z) _).
          refine (!(maponpathscomp0 gquot_inl_grpd _ _) @ _).
          refine (maponpaths (maponpaths gquot_inl_grpd) _).
          refine (path_assoc _ _ _ @ _).
          etrans.
          {
            refine (maponpaths (λ z, z @ _) _).
            refine (!(pathscomp0rid _) @ _).
            refine (maponpaths (λ z, (z @ _) @ _) _).
            exact (!(pathscomp0rid _)).
          }
          exact (!(eqtohomot (pstrans_comp IHP₁ f g) z)).
        }
        etrans.
        {
          refine (maponpaths (λ z, _ @ (_ @ z)) _).
          exact (maponpathscomp0 gquot_inl_grpd _ _).
        }
        do 2 (refine (path_assoc _ _ _ @ _)).
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        refine (!(path_assoc _ _ _) @ _).
        exact (sum_gquot_pstrans_comp_inl_help_two f g (IHP₁ X z)).
      + refine (!_).
        etrans.
        {
          refine (maponpaths (λ z, z @ _) (_ @ _)).
          { apply pathscomp0rid. }
          refine (maponpaths (λ z, z @ _) _).
          apply pathscomp0rid.
        }
        etrans.
        {
          refine (maponpaths (λ z, _ @ z) _).
          refine (maponpathscomp0 (sum_gquot_data_comp Z) _ _ @ _).
          etrans.
          {
            refine (maponpaths (λ z, z @ _) _).
            refine (maponpathscomp inr (sum_gquot_data_comp Z) _  @ _).
            exact (!(maponpathscomp (IHP₂ Z) gquot_inr_grpd _)).
          }
          etrans.
          {
            refine (maponpaths (λ z,
                                maponpaths
                                  gquot_inr_grpd
                                  (maponpaths
                                     (IHP₂ Z)
                                     _
                                  )
                                  @ z) _).
            refine (maponpathscomp inr (sum_gquot_data_comp Z) _  @ _).
            exact (!(maponpathscomp (IHP₂ Z) gquot_inr_grpd _)).
          }
          refine (!(maponpathscomp0 gquot_inr_grpd _ _) @ _).
          refine (maponpaths (maponpaths gquot_inr_grpd) _).
          exact (!(maponpathscomp0 (IHP₂ Z) _ _)).
        }
        etrans.
        {
          refine (maponpaths (λ z, (z @ _) @ _) _).
          exact ((maponpathscomp0 (gquot_functor_map _) _ _)).
        }
        do 2 (refine (!(path_assoc _ _ _) @ _)).
        etrans.
        {
          refine (maponpaths (λ z, _ @ z) _).
          etrans.
          {
            refine (maponpaths (λ z, _ @ z) _).
            refine (!(path_assoc _ _ _) @ _).
            refine (maponpaths (λ z, _ @ z) _).
            exact (!(maponpathscomp0 gquot_inr_grpd _ _)).
          }
          refine (path_assoc _ _ _ @ _).
          refine (maponpaths (λ z, z @ _) _).
          exact (sum_gquot_pstrans_comp_inr_help f g ((pr1 (psnaturality_of IHP₂ f)) z)).
        }
        etrans.
        {
          refine (maponpaths (λ z, _ @ z) _).
          refine (!(path_assoc _ _ _) @ _).
          refine (maponpaths (λ z, _ @ z) _).
          refine (!(maponpathscomp0 gquot_inr_grpd _ _) @ _).
          refine (maponpaths (maponpaths gquot_inr_grpd) _).
          refine (path_assoc _ _ _ @ _).
          etrans.
          {
            refine (maponpaths (λ z, z @ _) _).
            refine (!(pathscomp0rid _) @ _).
            refine (maponpaths (λ z, (z @ _) @ _) _).
            exact (!(pathscomp0rid _)).
          }
          exact (!(eqtohomot (pstrans_comp IHP₂ f g) z)).
        }
        etrans.
        {
          refine (maponpaths (λ z, _ @ (_ @ z)) _).
          exact (maponpathscomp0 gquot_inr_grpd _ _).
        }
        do 2 (refine (path_assoc _ _ _ @ _)).
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        refine (!(path_assoc _ _ _) @ _).
        exact (sum_gquot_pstrans_comp_inr_help_two f g (IHP₂ X z)).
  Qed.

  Definition sum_gquot
    : pstrans
        (ps_comp (⟦ P₁ + P₂ ⟧) gquot_psfunctor)
        (ps_comp gquot_psfunctor ⦃ P₁ + P₂ ⦄).
  Proof.
    use make_pstrans.
    - exact sum_gquot_data.
    - exact sum_gquot_is_pstrans.
  Defined.
End GQuotSum.
