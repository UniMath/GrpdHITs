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
      (gcleq (poly_act_groupoid P X) (poly_act_identity z))
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
             (gcleq (poly_act_groupoid P₁ X) (poly_act_identity a))
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
            (gcleq (poly_act_groupoid P₁ X) (poly_act_identity a))
            (gcleq (poly_act_groupoid P₂ X) g)
            @ _);
    refine (_ @ pathscomp0lid _);
    apply maponpaths_2;
    unfold uncurry;
    refine (!(maponpathscomp
                gquot_poly
                (λ z, z,, gquot_poly (gcl (poly_act_groupoid P₂ X) b₁))
                (gcleq (poly_act_groupoid P₁ X) (poly_act_identity a)))
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
             (gcleq (poly_act_groupoid P₂ X) (poly_act_identity b)) @ _);
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
            (gcleq (poly_act_groupoid P₂ X) (poly_act_identity b))
            @ _);
    refine (_ @ pathscomp0rid _);
    apply maponpaths;
    unfold uncurry;
    refine (!(maponpathscomp
                gquot_poly
                (λ z, gquot_poly (gcl (poly_act_groupoid P₁ X) a₂),, z)
                (gcleq (poly_act_groupoid P₂ X) (poly_act_identity b)))
             @ _);
    refine (ap_pair_r _ _ @ _);
    exact (maponpaths (pathsdirprod _)
                      (gquot_poly_poly_act_identity P₂ _))).
Defined.

Definition gquot_poly_poly_gquot_eq
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

Definition poly_gquot_gquot_poly_comp
           (P : poly_code)
           {X : groupoid}
           (a : poly_act_groupoid P X)
  : poly_gquot
      P X
      (gquot_poly (gcl (poly_act_groupoid P X) a))
    =
    gcl (poly_act_groupoid P X) a.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction a as [a | a].
    + exact (maponpaths gquot_inl_grpd (IHP₁ a)).
    + exact (maponpaths gquot_inr_grpd (IHP₂ a)).
  - exact (maponpaths
              (λ z, prod_gquot_comp z _) (IHP₁ (pr1 a))
            @ maponpaths
                (prod_gquot_comp _) (IHP₂ (pr2 a))).
Defined.

Definition poly_gquot_gquot_poly_po
           (P : poly_code)
           {X : groupoid}
           (a₁ a₂ : poly_act_groupoid P X)
           (g : poly_act_groupoid P X ⟦ a₁, a₂ ⟧)
  : @PathOver
      _ _ _
      (λ a, _)
      (poly_gquot_gquot_poly_comp P a₁)
      (poly_gquot_gquot_poly_comp P a₂)
      (gcleq (poly_act_groupoid P X) g).
Proof.
  use map_PathOver.
  refine (whisker_square
            (idpath _)
            (maponpathscomp _ (poly_gquot P X) _)
            (!(maponpathsidfun _))
            (idpath _)
            _).
  unfold square.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - induction g.
    rewrite ge.
    apply idpath.
  - refine (pathscomp0rid _ @ _).
    etrans.
    {
      apply maponpaths.
      apply gquot_rec_beta_gcleq.
    }
    apply gquot_rec_beta_gcleq.
  - induction a₁ as [a₁ | a₁], a₂ as [a₂ | a₂].
    + specialize (IHP₁ a₁ a₂ g) ; clear IHP₂.
      refine (_ @ maponpaths (maponpaths gquot_inl_grpd) IHP₁ @ _).
      * refine (!_).
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (gquot_rec_beta_gcleq (poly_act_groupoid (P₁ + P₂) X) _ _ _ _ _ _ _ _ g).
        }
        etrans.
        {
          apply (maponpathscomp
                   (λ z, inl (gquot_poly z))
                   ((sum_gquot (poly_gquot P₁) (poly_gquot P₂)) X)).
        }
        refine (!_).
        etrans.
        {
          apply maponpathscomp.
        }
        apply (maponpathscomp
                 gquot_poly
                 (λ x, gquot_inl_grpd (poly_gquot P₁ X x))).
      * etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        apply gquot_rec_beta_gcleq.
    + exact (fromempty g).
    + exact (fromempty g).
    + specialize (IHP₂ a₁ a₂ g) ; clear IHP₁.
      refine (_ @ maponpaths (maponpaths gquot_inr_grpd) IHP₂ @ _).
      * refine (!_).
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (gquot_rec_beta_gcleq (poly_act_groupoid (P₁ + P₂) X) _ _ _ _ _ _ _ _ g).
        }
        etrans.
        {
          apply (maponpathscomp
                   (λ z, inr (gquot_poly z))
                   ((sum_gquot (poly_gquot P₁) (poly_gquot P₂)) X)).
        }
        refine (!_).
        etrans.
        {
          apply maponpathscomp.
        }
        apply (maponpathscomp
                 gquot_poly
                 (λ x, gquot_inr_grpd (poly_gquot P₂ X x))).
      * etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        apply gquot_rec_beta_gcleq.
  - specialize (IHP₁ _ _ (pr1 g)).
    specialize (IHP₂ _ _ (pr2 g)).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        pose (uncurry_ap
                prod_gquot_comp
                (poly_gquot_gquot_poly_comp P₁ (pr1 a₂))
                (poly_gquot_gquot_poly_comp P₂ (pr2 a₂)))
          as h.
        unfold uncurry in h.
        exact (!h).
      }
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathscomp
                   (dirprodf (poly_gquot P₁ X) (poly_gquot P₂ X))
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (maponpaths
                      (gquot_prod gquot_poly gquot_poly)
                      (gcleq (poly_act_groupoid (P₁ * P₂) X) g)))).
      }
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply gquot_rec_beta_gcleq.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (!(maponpaths_pathsdirprod _ _ _ _)).
      }      
      exact (!(maponpathscomp0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (maponpaths
                       ((poly_gquot P₁) X)
                       (maponpaths
                          gquot_poly
                          (gcleq (poly_act_groupoid P₁ X) (pr1 g))))
                    (maponpaths
                       ((poly_gquot P₂) X)
                       (maponpaths
                          gquot_poly
                          (gcleq (poly_act_groupoid P₂ X) (pr2 g)))))
                 (pathsdirprod
                    (poly_gquot_gquot_poly_comp P₁ (pr1 a₂))
                    (poly_gquot_gquot_poly_comp P₂ (pr2 a₂))))).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply pathsdirprod_concat.
      }
      etrans.
      {
        apply maponpaths.
        exact IHP₂.
      }
      apply maponpaths_2.
      exact IHP₁.
    }
    etrans.
    {
      apply maponpaths.
      exact (!(pathsdirprod_concat _ _ _ _)).
    }
    etrans.
    {
      exact (maponpathscomp0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod
                  (poly_gquot_gquot_poly_comp P₁ (pr1 a₁))
                  (poly_gquot_gquot_poly_comp P₂ (pr2 a₁)))
               (pathsdirprod
                  (gcleq (poly_act_groupoid P₁ X) (pr1 g))
                  (gcleq (poly_act_groupoid P₂ X) (pr2 g)))).
    }
    etrans.
    {
      apply maponpaths_2.
      pose (uncurry_ap
              prod_gquot_comp
              (poly_gquot_gquot_poly_comp P₁ (pr1 a₁))
              (poly_gquot_gquot_poly_comp P₂ (pr2 a₁)))
        as h.
      unfold uncurry in h.
      exact h.
    }
    apply maponpaths.
    etrans.
    {
      pose (uncurry_ap
              prod_gquot_comp
              (gcleq (poly_act_groupoid P₁ X) (pr1 g))
              (gcleq (poly_act_groupoid P₂ X) (pr2 g)))
        as h.
      unfold uncurry in h.
      exact h.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (gquot_double_rec'_beta_l_gcleq _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      apply maponpaths.
      exact (gquot_double_rec'_beta_r_gcleq _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    }
    refine (!(gconcat _ _ _) @ _).
    apply maponpaths.
    exact (pathsdirprod
             (poly_act_id_right _)
             (poly_act_id_left _)).
Qed.

Definition poly_gquot_gquot_poly_eq
           (P : poly_code)
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P X)), poly_gquot P X (gquot_poly z) = z.
Proof.
  use gquot_ind_set.
  - exact (poly_gquot_gquot_poly_comp P).
  - exact (poly_gquot_gquot_poly_po P).
  - exact (λ _, gtrunc _ _ _).
Defined.

Definition poly_gquot_isweq
           (P : poly_code)
           (X : groupoid)
  : isweq (poly_gquot P X).
Proof.
  use gradth.
  - exact (@gquot_poly P X).
  - exact (gquot_poly_poly_gquot_eq P).
  - exact (poly_gquot_gquot_poly_eq P).
Defined.

Definition gquot_poly_poly_gquot
           {P : poly_code}
           {X : groupoid}
  : ∏ (z : poly_act P (gquot X)), gquot_poly (poly_gquot P X z) = z
  := gquot_poly_poly_gquot_eq P.

Definition poly_gquot_gquot_poly
           {P : poly_code}
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P X)), poly_gquot P X (gquot_poly z) = z
  := poly_gquot_gquot_poly_eq P.

Definition maponpaths_gquot_poly_poly_gquot_inl
           (P₁ P₂ : poly_code)
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P₁ X)),
    maponpaths
      (sum_gquot_data_comp (poly_gquot P₁) (poly_gquot P₂) X)
      (inl_gquot_poly P₁ P₂ z)
    @ maponpaths
        gquot_inl_grpd
        (poly_gquot_gquot_poly z)
    =
    poly_gquot_gquot_poly (gquot_inl_grpd z).
Proof.
  use gquot_ind_prop.
  - exact (λ _, idpath _).
  - exact (λ _, gtrunc _ _ _ _ _).
Qed.

Definition maponpaths_gquot_poly_poly_gquot_inr
           (P₁ P₂ : poly_code)
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P₂ X)),
    maponpaths
      (sum_gquot_data_comp (poly_gquot P₁) (poly_gquot P₂) X)
      (inr_gquot_poly P₁ P₂ z)
    @ maponpaths
        gquot_inr_grpd
        (poly_gquot_gquot_poly z)
    =
    poly_gquot_gquot_poly (gquot_inr_grpd z).
Proof.
  use gquot_ind_prop.
  - exact (λ _, idpath _).
  - exact (λ _, gtrunc _ _ _ _ _).
Qed.

Definition maponpaths_gquot_poly_poly_gquot_pair
           (P₁ P₂ : poly_code)
           {X : groupoid}
  : ∏ (z₁ : gquot (poly_act_groupoid P₁ X))
      (z₂ : gquot (poly_act_groupoid P₂ X)),
    maponpaths
      (prod_gquot (poly_gquot P₁) (poly_gquot P₂) X)
      (gquot_poly_pair
         P₁ P₂
         z₁
         z₂)
    @ maponpaths
        (λ z0,
         prod_gquot_comp
           z0
           (poly_gquot P₂ X (gquot_poly z₂)))
        (poly_gquot_gquot_poly z₁)
    @ maponpaths
        (prod_gquot_comp z₁)
        (poly_gquot_gquot_poly z₂)
  =
  poly_gquot_gquot_poly (prod_gquot_comp z₁ z₂).
Proof.
  use gquot_double_ind_prop.
  - exact (λ _ _, gtrunc _ _ _ _ _).
  - intros a b.
    apply idpath.
Qed.

Definition maponpaths_gquot_poly_poly_gquot
           (P : poly_code)
           {X : groupoid}
           (z : poly_act P (gquot X))
  : maponpaths (poly_gquot P X) (gquot_poly_poly_gquot z)
    =
    poly_gquot_gquot_poly (poly_gquot P X z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_prop.
    + intro a.
      apply idpath.
    + exact (λ _, gtrunc _ _ _ _ _).
  - induction z as [z | z].
    + etrans.
      {
        exact (maponpathscomp0
                 (sum_gquot (poly_gquot P₁) (poly_gquot P₂) X)
                 (inl_gquot_poly P₁ P₂ (poly_gquot P₁ X z))
                 (maponpaths inl (gquot_poly_poly_gquot z))).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpathscomp.
        }
        etrans.
        {
          exact (!(maponpathscomp (poly_gquot P₁ X) gquot_inl_grpd _)).
        }
        apply maponpaths.
        apply IHP₁.
      }
      exact (maponpaths_gquot_poly_poly_gquot_inl P₁ P₂ _).
    + etrans.
      {
        exact (maponpathscomp0
                 (sum_gquot (poly_gquot P₁) (poly_gquot P₂) X)
                 (inr_gquot_poly P₁ P₂ (poly_gquot P₂ X z))
                 (maponpaths inr (gquot_poly_poly_gquot z))).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpathscomp.
        }
        etrans.
        {
          exact (!(maponpathscomp (poly_gquot P₂ X) gquot_inr_grpd _)).
        }
        apply maponpaths.
        apply IHP₂.
      }
      exact (maponpaths_gquot_poly_poly_gquot_inr P₁ P₂ _).
  - etrans.
    {
      exact (maponpathscomp0
               (prod_gquot (poly_gquot P₁) (poly_gquot P₂) X)
               (gquot_poly_pair
                  P₁ P₂
                  (poly_gquot P₁ X (pr1 z))
                  (poly_gquot P₂ X (pr2 z)))
               (pathsdirprod
                  (gquot_poly_poly_gquot (pr1 z))
                  (gquot_poly_poly_gquot (pr2 z)))).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        exact (!(maponpathscomp
                   (dirprodf (poly_gquot P₁ X) (poly_gquot P₂ X))
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod
                      (gquot_poly_poly_gquot (pr1 z))
                      (gquot_poly_poly_gquot (pr2 z))))).
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpaths_pathsdirprod.
      }
      pose (uncurry_ap
              prod_gquot_comp
              (maponpaths
                 (poly_gquot P₁ X)
                 (gquot_poly_poly_gquot (pr1 z)))
              (maponpaths
                 (poly_gquot P₂ X)
                 (gquot_poly_poly_gquot (pr2 z))))
        as h.
      unfold uncurry in h.
      exact h.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply IHP₁.
    }
    etrans.
    {
      do 3 apply maponpaths.
      apply IHP₂.
    }
    exact (maponpaths_gquot_poly_poly_gquot_pair P₁ P₂ _ _).
Qed.

Definition maponpaths_poly_gquot_gquot_poly
           (P : poly_code)
           {X : groupoid}
           (x : gquot (poly_act_groupoid P X))
  : maponpaths (@gquot_poly P X) (poly_gquot_gquot_poly x)
    =
    gquot_poly_poly_gquot (gquot_poly x)
  := other_adjoint
       (poly_gquot P X)
       gquot_poly
       poly_gquot_gquot_poly
       gquot_poly_poly_gquot
       (maponpaths_gquot_poly_poly_gquot P)
       x.

(*
Definition poly_gquot_weq
           (P : poly_code)
           (X : groupoid)
  : poly_act P (gquot X) ≃ gquot (poly_act_groupoid P X)
  := make_weq _ (poly_gquot_isweq P X).

Definition gquot_poly_poly_gquot
           {P : poly_code}
           {X : groupoid}
  : ∏ (z : poly_act P (gquot X)), gquot_poly (poly_gquot P X z) = z
  := homotinvweqweq (poly_gquot_weq P X).

Definition poly_gquot_gquot_poly
           {P : poly_code}
           {X : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P X)), poly_gquot P X (gquot_poly z) = z
  := homotweqinvweq (poly_gquot_weq P X).

Definition maponpaths_gquot_poly_poly_gquot
           (P : poly_code)
           {X : groupoid}
           (z : poly_act P (gquot X))
  : maponpaths (poly_gquot P X) (gquot_poly_poly_gquot z)
    =
    poly_gquot_gquot_poly (poly_gquot P X z)
  := homotweqinvweqweq (poly_gquot_weq P X) z.

Definition maponpaths_poly_gquot_gquot_poly
           (P : poly_code)
           {X : groupoid}
           (x : gquot (poly_act_groupoid P X))
  : maponpaths (@gquot_poly P X) (poly_gquot_gquot_poly x)
    =
    gquot_poly_poly_gquot (gquot_poly x)
  := homotweqweqinvweq (poly_gquot_weq P X) x.
*)
