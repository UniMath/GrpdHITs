(** Commutation of groupoid quotient with polynomials *)
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
Require Import hit_biadjunction.gquot_natural.

Require Export hit_biadjunction.gquot_commute.gquot_commute_const_id.
Require Export hit_biadjunction.gquot_commute.gquot_commute_sum.
Require Export hit_biadjunction.gquot_commute.gquot_commute_prod.

Local Open Scope cat.

Opaque ps_comp.

(*
Local Definition TODO {A : UU} : A.
Admitted.
 *)

Definition maponpaths_homot
           {A B : UU}
           {f g : A → B}
           (e : f ~ g)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : maponpaths f p = e a₁ @ maponpaths g p @ !(e a₂).
Proof.
  induction p.
  exact (!(pathsinv0r (e a₁))).
Defined.

(** Commutation of groupoid quotient with polynomials *)
Definition poly_gquot
           (P : poly_code)
  : pstrans
      (ps_comp
         (⟦ P ⟧)
         gquot_psfunctor)
      (ps_comp
         gquot_psfunctor
         ⦃ P ⦄).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (const_gquot A).
  - exact id_gquot.
  - exact (sum_gquot IHP₁ IHP₂).
  - exact (prod_gquot IHP₁ IHP₂).
Defined.

(** `poly_gquot` and `gquot_poly` compose to the identity *)
(*
Definition const_gquot_gquot_const
           (A : one_type)
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid (C A) X)),
    (const_gquot A) X (gquot_const A X z) = z.
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ;
       induction g ;
       apply map_PathOver ;
       refine (pathscomp0rid _ @ _ @ !(maponpathsidfun _)) ;
       refine (!(maponpathscomp
                   (gquot_const A X)
                   (const_gquot A X)
                   (gcleq (poly_act_groupoid (C A) X) _))
                @ _) ;
       refine (maponpaths (maponpaths _) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _) @ _) ;
       exact (!(ge _ _))).
  - intro ; exact (gtrunc _ _ _).
Defined.

Definition id_gquot_gquot_id
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid I X)), id_gquot X (gquot_id X z) = z.
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ;
       use map_PathOver ;
       refine (pathscomp0rid _ @ _ @ !(maponpathsidfun _));
       refine (!(maponpathscomp
                   (gquot_id X)
                   (id_gquot X)
                   (gcleq (poly_act_groupoid I X) _))
                @ _);
       refine (maponpaths (maponpaths _) (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _) @ _);
       apply gquot_rec_beta_gcleq).
  - intro ; exact (gtrunc _ _ _).
Defined.

Definition sum_gquot_gquot_sum_comp
           {P₁ P₂ : poly_code}
           {X : groupoid}
           (IHP₁ : ∏ (z : gquot (poly_act_groupoid P₁ X)),
                   (poly_gquot P₁) X (gquot_poly z) = z)
           (IHP₂ : ∏ (z : gquot (poly_act_groupoid P₂ X)),
                   (poly_gquot P₂) X (gquot_poly z) = z)
  : ∏ (z : poly_act_groupoid (P₁ + P₂) X),
    sum_gquot
      (poly_gquot P₁) (poly_gquot P₂) X
      (gquot_sum gquot_poly gquot_poly (gcl _ z))
    =
    gcl _ z.
Proof.
  intros z.
  induction z as [z | z].
  - exact (maponpaths gquot_inl_grpd (IHP₁ (gcl (poly_act_groupoid P₁ X) z))).
  - exact (maponpaths gquot_inr_grpd (IHP₂ (gcl (poly_act_groupoid P₂ X) z))).
Defined.

Definition sum_gquot_gquot_sum_po
           {P₁ P₂ : poly_code}
           {X : groupoid}
           (IHP₁ : ∏ (z : gquot (poly_act_groupoid P₁ X)),
                   (poly_gquot P₁) X (gquot_poly z) = z)
           (IHP₂ : ∏ (z : gquot (poly_act_groupoid P₂ X)),
                   (poly_gquot P₂) X (gquot_poly z) = z)
           (a₁ a₂ : poly_act_groupoid (P₁ + P₂) X)
           (g : poly_act_groupoid (P₁ + P₂) X ⟦ a₁, a₂ ⟧)
  : @PathOver
      _ _ _
      (λ _, _)
      (sum_gquot_gquot_sum_comp IHP₁ IHP₂ a₁)
      (sum_gquot_gquot_sum_comp IHP₁ IHP₂ a₂)
      (gcleq (poly_act_groupoid (P₁ + P₂) X) g).
Proof.
  induction a₁ as [a₁ | a₁], a₂ as [a₂ | a₂].
  - apply map_PathOver.
    refine (whisker_square
              (idpath _)                
              _
              (!(maponpathsidfun _))
              (idpath _)
              _).
    {
      refine (!_ @ (maponpathscomp
                      (gquot_sum gquot_poly gquot_poly)
                      (sum_gquot (poly_gquot P₁) (poly_gquot P₂) X)
                      (gcleq (poly_act_groupoid (P₁ + P₂) X) g))
             ).
      etrans.
      {
        apply maponpaths.
        refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _).
        exact (!(maponpathscomp
                   gquot_poly
                   inl
                   (gcleq (poly_act_groupoid P₁ X) g))).
      }
      refine (maponpathscomp
                inl
                _
                _
                @ _).
      refine (!(maponpathscomp
                  (poly_gquot P₁ X)
                  gquot_inl_grpd
                  (maponpaths gquot_poly (gcleq (poly_act_groupoid P₁ X) g)))
               @ _).
      etrans.
      {
        apply maponpaths.
        refine (maponpathscomp _ _ _ @ _).
        refine (maponpaths_homot IHP₁ _ @ _).
        apply maponpaths ; apply maponpaths_2.
        apply maponpathsidfun.
      }
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths_2.
      apply gquot_rec_beta_gcleq.
    }
    unfold square.
    refine (!(path_assoc _ _ _)
             @ maponpaths
             (λ z, _ @ z)
             (!(path_assoc _ _ _)
               @ maponpaths (λ z, _ @ z) _
               @ pathscomp0rid _)).
    refine (!(maponpathscomp0
                gquot_inl_grpd
                (! IHP₁ (gcl (poly_act_groupoid P₁ X) a₂))
                (IHP₁ (gcl (poly_act_groupoid P₁ X) a₂)))
             @ _).
    exact (maponpaths
             (maponpaths gquot_inl_grpd)
             (pathsinv0l (IHP₁ (gcl (poly_act_groupoid P₁ X) a₂)))).
  - exact (fromempty g).
  - exact (fromempty g).
  - apply map_PathOver.
    refine (whisker_square
              (idpath _)                
              _
              (!(maponpathsidfun _))
              (idpath _)
              _).
    {
      refine (!_ @ (maponpathscomp
                      (gquot_sum gquot_poly gquot_poly)
                      (sum_gquot (poly_gquot P₁) (poly_gquot P₂) X)
                      (gcleq (poly_act_groupoid (P₁ + P₂) X) g))
             ).
      etrans.
      {
        apply maponpaths.
        refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _).
        exact (!(maponpathscomp
                   gquot_poly
                   inr
                   (gcleq (poly_act_groupoid P₂ X) g))).
      }
      refine (maponpathscomp
                inr
                _
                _
                @ _).
      refine (!(maponpathscomp
                  (poly_gquot P₂ X)
                  gquot_inr_grpd
                  (maponpaths gquot_poly (gcleq (poly_act_groupoid P₂ X) g)))
               @ _).
      etrans.
      {
        apply maponpaths.
        refine (maponpathscomp _ _ _ @ _).
        refine (maponpaths_homot IHP₂ _ @ _).
        apply maponpaths ; apply maponpaths_2.
        apply maponpathsidfun.
      }
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths_2.
      apply gquot_rec_beta_gcleq.
    }
    unfold square.
    refine (!(path_assoc _ _ _)
             @ maponpaths
             (λ z, _ @ z)
             (!(path_assoc _ _ _)
               @ maponpaths (λ z, _ @ z) _
               @ pathscomp0rid _)).
    refine (!(maponpathscomp0
                gquot_inr_grpd
                (! IHP₂ (gcl (poly_act_groupoid P₂ X) a₂))
                (IHP₂ (gcl (poly_act_groupoid P₂ X) a₂)))
             @ _).
    exact (maponpaths
             (maponpaths gquot_inr_grpd)
             (pathsinv0l (IHP₂ (gcl (poly_act_groupoid P₂ X) a₂)))).
Qed.

Definition sum_gquot_gquot_sum
           {P₁ P₂ : poly_code}
           {X : groupoid}
           (IHP₁ : ∏ (z : gquot (poly_act_groupoid P₁ X)),
                   (poly_gquot P₁) X (gquot_poly z) = z)
           (IHP₂ : ∏ (z : gquot (poly_act_groupoid P₂ X)),
                   (poly_gquot P₂) X (gquot_poly z) = z)
  : ∏ (z : gquot (poly_act_groupoid (P₁ + P₂) X)),
    sum_gquot
      (poly_gquot P₁) (poly_gquot P₂) X
      (gquot_sum gquot_poly gquot_poly z)
    =
    z.
Proof.
  use gquot_ind_set.
  - exact (sum_gquot_gquot_sum_comp IHP₁ IHP₂).
  - exact (sum_gquot_gquot_sum_po IHP₁ IHP₂).
  - intro ; exact (gtrunc _ _ _).
Defined.

Definition poly_gquot_gquot_poly
           (P : poly_code)
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P X)), poly_gquot P X (gquot_poly z) = z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (const_gquot_gquot_const A).
  - exact id_gquot_gquot_id.
  - exact (sum_gquot_gquot_sum IHP₁ IHP₂).
  - apply TODO.
Defined.
*)
(** Other direction *)
Definition gquot_id_id_gquot
           {X : groupoid}
  : ∏ (z : gquot X), gquot_id X (id_gquot X z) = z.
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ;
       apply map_PathOver ;
       exact (whisker_square
                (idpath _)
                (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                  @ maponpaths _ (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                  @ maponpathscomp (id_gquot X) (gquot_id X) (gcleq X g))
                (!(maponpathsidfun _))
                (idpath _)
                (vrefl _))).
  - intro ; exact (gtrunc _ _ _).
Defined.

Definition inl_gquot_poly
           (P₁ P₂ : poly_code)
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P₁ X)),
    @gquot_sum P₁ P₂ _ gquot_poly gquot_poly (gquot_inl_grpd z)
    =
    inl (gquot_poly z).
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ;
       apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ maponpaths
                   (maponpaths (gquot_sum gquot_poly gquot_poly))
                   (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 @ maponpathscomp
                   gquot_inl_grpd
                   (gquot_sum gquot_poly gquot_poly)
                   (gcleq (poly_act_groupoid P₁ X) g))
                 (idpath _)
                 (idpath _)
                 _) ;
       apply pathscomp0rid).
  - intro.
    exact (isofhlevelssncoprod
            1
            (poly_act P₁ (gquot X))
            (poly_act P₂ (gquot X))
            (poly_act_hlevel P₁ (make_one_type _ (gtrunc X)))
            (poly_act_hlevel P₂ (make_one_type _ (gtrunc X)))
            _
            _).
Defined.

Definition inr_gquot_poly
           (P₁ P₂ : poly_code)
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P₂ X)),
    @gquot_sum P₁ P₂ _ gquot_poly gquot_poly (gquot_inr_grpd z)
    =
    inr (gquot_poly z).
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ;
       apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ maponpaths
                   (maponpaths (gquot_sum gquot_poly gquot_poly))
                   (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 @ maponpathscomp
                   gquot_inr_grpd
                   (gquot_sum gquot_poly gquot_poly)
                   (gcleq (poly_act_groupoid P₂ X) g))
                 (idpath _)
                 (idpath _)
                 _) ;
       apply pathscomp0rid).
  - intro.
    exact (isofhlevelssncoprod
            1
            (poly_act P₁ (gquot X))
            (poly_act P₂ (gquot X))
            (poly_act_hlevel P₁ (make_one_type _ (gtrunc X)))
            (poly_act_hlevel P₂ (make_one_type _ (gtrunc X)))
            _
            _).
Defined.

Definition gquot_poly_poly_act_identity
           (P : poly_code)
           {X : groupoid}
           (z : poly_act P X)
  : maponpaths
      gquot_poly
      (gcleq (poly_act_groupoid P X) (poly_act_identity P X z))
    =
    idpath _.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (maponpaths (maponpaths _) (ge _ _)).
  - exact (maponpaths (maponpaths _) (ge _ _)).
  - induction z as [z | z].
    + refine (_ @ maponpaths (maponpaths inl) (IHP₁ z)).
      refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _).
      exact (!(maponpathscomp gquot_poly inl _)).
    + refine (_ @ maponpaths (maponpaths inr) (IHP₂ z)).
      refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _).
      exact (!(maponpathscomp gquot_poly inr _)).
  - refine (_ @ maponpaths
                  (λ z, pathsdirprod z (idpath _))
                  (IHP₁ (pr1 z))).
    refine (_ @ maponpaths
                  (pathsdirprod _)
                  (IHP₂ (pr2 z))).
    refine (_ @ !(maponpaths_pathsdirprod _ _ _ _)).
    refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _).
    exact (maponpaths_pathsdirprod _ _ _ _).
Qed.
    
Definition gquot_poly_pair
           (P₁ P₂ : poly_code)
           {X : groupoid}
  : ∏ (z₁ : gquot (poly_act_groupoid P₁ X))
      (z₂ : gquot (poly_act_groupoid P₂ X)),
    gquot_poly (prod_gquot_comp z₁ z₂)
    =
    gquot_poly z₁ ,, gquot_poly z₂.
Proof.
  use gquot_double_ind_set.
  - intros a b.
    exact (isofhleveldirprod
            3
            (poly_act P₁ (gquot X))
            (poly_act P₂ (gquot X))
            (poly_act_hlevel P₁ (make_one_type _ (gtrunc X)))
            (poly_act_hlevel P₂ (make_one_type _ (gtrunc X)))
            _
            _).
  - exact (λ _ _, idpath _).
  - abstract
    (intros a b₁ b₂ g;
    apply map_PathOver;
    refine (whisker_square
              (idpath _)
              (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
              @ (maponpaths
                   (maponpaths gquot_poly)
                   (!(gquot_double_rec'_beta_r_gcleq
                        (poly_act_groupoid P₁ X)
                        (poly_act_groupoid P₂ X)
                        _ _ _ _ _ _ _ _ _ _ _ g)))
              @ maponpathscomp
                  (prod_gquot_comp (gcl (poly_act_groupoid P₁ X) a))
                  gquot_poly
                  (gcleq (poly_act_groupoid P₂ X) g))
              (idpath _)
              (idpath _)
              _);
    unfold square;
    refine (pathscomp0rid _ @ _ @ !(pathscomp0lid _));
    refine (maponpaths_pathsdirprod
             (@gquot_poly P₁ X)
             (@gquot_poly P₂ X)
             (gcleq (poly_act_groupoid P₁ X) (poly_act_identity P₁ X a))
             (gcleq (poly_act_groupoid P₂ X) g) @ _);
    unfold dirprodf;
    refine (@uncurry_ap
            (gquot (poly_act_groupoid P₁ X))
            (gquot (poly_act_groupoid P₂ X))
            (poly_act P₁ (gquot X) × poly_act P₂ (gquot X))
            (λ (x : gquot (poly_act_groupoid P₁ X))
               (y : gquot (poly_act_groupoid P₂ X)),
             (gquot_poly x ,, gquot_poly y))
            _ _ _ _
            (gcleq (poly_act_groupoid P₁ X) (poly_act_identity P₁ X a))
            (gcleq (poly_act_groupoid P₂ X) g)
            @ _);
    refine (_ @ pathscomp0lid _);
    apply maponpaths_2;
    unfold uncurry;
    refine (!(maponpathscomp
                gquot_poly
                (λ z, z,, gquot_poly (gcl (poly_act_groupoid P₂ X) b₁))
                (gcleq (poly_act_groupoid P₁ X) (poly_act_identity P₁ X a)))
             @ _);
    refine (ap_pair_l _ _ @ _);
    exact (maponpaths (λ z, pathsdirprod z _)
                      (gquot_poly_poly_act_identity P₁ _))).
  - abstract
    (intros a₁ a₂ b g;
    apply map_PathOver;
    refine (whisker_square
              (idpath _)
              (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                @ (maponpaths
                   (maponpaths gquot_poly)
                   _)
                @ maponpathscomp
                    (λ z, prod_gquot_comp z (gcl (poly_act_groupoid P₂ X) b))
                    gquot_poly
                    (gcleq (poly_act_groupoid P₁ X) g))
              (idpath _)
              (idpath _)
              _)
    ; [ exact (!(gquot_double_rec'_beta_l_gcleq
                   (poly_act_groupoid P₁ X)
                   (poly_act_groupoid P₂ X)
                   _ _ _ _ _ _ _ _ _ _
                   b g)) | ];
    unfold square;
    refine (pathscomp0rid _ @ _ @ !(pathscomp0lid _));
    refine (maponpaths_pathsdirprod
             (@gquot_poly P₁ X)
             (@gquot_poly P₂ X)
             (gcleq (poly_act_groupoid P₁ X) g)
             (gcleq (poly_act_groupoid P₂ X) (poly_act_identity P₂ X b)) @ _);
    unfold dirprodf;
    refine (@uncurry_ap
            (gquot (poly_act_groupoid P₁ X))
            (gquot (poly_act_groupoid P₂ X))
            (poly_act P₁ (gquot X) × poly_act P₂ (gquot X))
            (λ (x : gquot (poly_act_groupoid P₁ X))
               (y : gquot (poly_act_groupoid P₂ X)),
             (gquot_poly x ,, gquot_poly y))
            _ _ _ _
            (gcleq (poly_act_groupoid P₁ X) g)
            (gcleq (poly_act_groupoid P₂ X) (poly_act_identity P₂ X b))
            @ _);
    refine (_ @ pathscomp0rid _);
    apply maponpaths;
    unfold uncurry;
    refine (!(maponpathscomp
                gquot_poly
                (λ z, gquot_poly (gcl (poly_act_groupoid P₁ X) a₂),, z)
                (gcleq (poly_act_groupoid P₂ X) (poly_act_identity P₂ X b)))
             @ _);
    refine (ap_pair_r _ _ @ _);
    exact (maponpaths (pathsdirprod _)
                      (gquot_poly_poly_act_identity P₂ _))).
Defined.

Definition gquot_poly_poly_gquot
           (P : poly_code)
           {X : groupoid}
  : ∏ (z : poly_act P (gquot X)), gquot_poly (poly_gquot P X z) = z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact idpath.
  - exact gquot_id_id_gquot.
  - intro z.
    induction z as [z | z].
    + exact (inl_gquot_poly P₁ P₂ _ @ maponpaths inl (IHP₁ z)).
    + exact (inr_gquot_poly P₁ P₂ _ @ maponpaths inr (IHP₂ z)).
  - intro z.
    refine (_ @ pathsdirprod (IHP₁ (pr1 z) ) (IHP₂ (pr2 z))).
    exact (gquot_poly_pair
             P₁ P₂
             (poly_gquot P₁ X (pr1 z))
             (poly_gquot P₂ X (pr2 z))).
Defined.
