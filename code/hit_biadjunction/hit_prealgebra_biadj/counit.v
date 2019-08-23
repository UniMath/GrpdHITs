Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.
Require Import biadjunctions.all.
Require Import hit_biadjunction.hit_prealgebra_biadj.biadj_data.

Local Open Scope cat.

Local Definition TODO {A : UU} : A.
Admitted.

Definition homotsec_natural
           {A B : UU}
           {f g : A → B}
           (e : f ~ g)
           {a₁ a₂ : A}
           (p : a₂ = a₁)
  : e a₁ = maponpaths f (!p) @ e a₂ @ maponpaths g p.
Proof.
  induction p.
  exact (!(pathscomp0rid _)).
Defined.

Definition pathsdirprod_inv
           {A B : UU}
           {a₁ a₂ : A} {b₁ b₂ : B}
           (p : a₁ = a₂) (q : b₁ = b₂)
  : ! (pathsdirprod p q) = pathsdirprod (! p) (! q).
Proof.
  induction p ; induction q.
  apply idpath.
Defined.

Section CounitNat.
  Local Arguments idpath {_ _}.
  Local Arguments nat_trans_comp {_ _ _ _ _} _ _.
  Local Arguments nat_trans_id {_ _ _}.
  Local Notation "'ap'" := maponpaths.
  Local Notation "'GQ₀'" := gquot_functor_obj.
  Local Notation "'GQ₁'" := gquot_functor_map.
  Local Notation "'GQ₂'" := gquot_functor_cell.
  Local Notation "'GQC'" := gquot_functor_composition.
  Local Notation "'PA₀'" := poly_act.
  Local Notation "'PA₁'" := poly_map.
  Local Notation "'PA₂'" := poly_act_nat_trans_data.
  Local Notation "'PAC'" := poly_act_functor_composition_data.

  Definition PA₁_gquot_counit_map
             {P : poly_code}
             {X Y : one_type}
             (f : X → Y)
             (z : PA₀ P (gquot (one_type_to_groupoid X)))
    : PA₁ P f (PA₁ P (gquot_counit_map X) z)
      =
      PA₁ P (gquot_counit_map Y) (PA₁ P (GQ₁ (function_to_functor f)) z).
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact idpath.
    - revert z.
      use gquot_ind_set.
      + intro.
        exact idpath.
      + abstract
          (intros a₁ a₂ g ;
           induction g ;
           rewrite ge ;
           apply identityPathOver).
      + intro.
        exact (one_type_isofhlevel Y _ _).
    - induction z as [z | z].
      + exact (maponpaths inl (IHP₁ z)).
      + exact (maponpaths inr (IHP₂ z)).
    - use pathsdirprod.
      + exact (IHP₁ (pr1 z)).
      + exact (IHP₂ (pr2 z)).
  Defined.

  Definition poly_path_groupoid_is_id
             {P : poly_code}
             {X : one_type}
             (z : PA₀ P X)
    : pr1 (pr111 (poly_path_groupoid P) X) z
      =
      z.
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction z as [z | z].
      + exact (ap inl (IHP₁ z)).
      + exact (ap inr (IHP₂ z)).
    - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
  Defined.

  Definition algebra_biadjunction_lift_counit_pstrans_GQ_nat
             {P : poly_code}
             {x y : one_types}
             (f : one_types ⟦ x, y ⟧)
             {xx : (disp_alg_bicat (⟦ P ⟧)) x}
             {yy : (disp_alg_bicat (⟦ P ⟧)) y}
             (na : ((poly_path_groupoid
                       P x
                       ∙ function_to_functor xx)
                      ∙ function_to_functor f)
                     ⟹
                     (poly_act_functor
                        P _ _ (function_to_functor f)
                        ∙ (poly_path_groupoid P y ∙ function_to_functor yy)))

    : ∏ (z : gquot (poly_act_groupoid P (one_type_to_groupoid x))),
      f
        (xx
           (gquot_counit_map
              (make_one_type (PA₀ P _) (poly_act_hlevel P x))
              (GQ₁ ((poly_path_groupoid P) x) z)))
      =
      yy
        (gquot_counit_map
           (make_one_type (PA₀ P _) (poly_act_hlevel P y))
           (GQ₁ ((poly_path_groupoid P) y)
                (GQ₁
                   (poly_act_functor
                      P (one_type_to_groupoid x) (one_type_to_groupoid y)
                      (function_to_functor f)) z))).
  Proof.
    use gquot_ind_set.
    - exact (λ a, na a).
    -intros a₁ a₂ g.
      use map_PathOver.
      refine (whisker_square
                idpath
                _
                _
                idpath
                _).
     + refine (!_).
       refine (!(maponpathscomp
                   _
                   _
                   _) @ _).
       apply ap.
       refine (!(maponpathscomp
                   _
                   _
                   _) @ _).
       apply ap.
       refine (!(maponpathscomp
                   _
                   _
                   _) @ _).
       etrans.
       {
         apply ap.
         apply gquot_rec_beta_gcleq.
       }
       apply gquot_rec_beta_gcleq.
     + refine (!_).
       refine (!(maponpathscomp
                   _
                   _
                   _) @ _).
       apply ap.
       refine (!(maponpathscomp
                   (λ z, GQ₁ _ (GQ₁ _ z))
                   (gquot_counit_map _)
                   _) @ _).
       etrans.
       {
         apply ap.
         refine (!(maponpathscomp
                     _
                     _
                     _) @ _).
         etrans.
         {
           apply ap.
           apply gquot_rec_beta_gcleq.
         }
         apply gquot_rec_beta_gcleq.
       }
       apply gquot_rec_beta_gcleq.
     + exact (pr2 na _ _ g).
    - intro.
      exact (one_type_isofhlevel y _ _).
  Defined.

  Definition poly_path_groupoid_gquot_counit_map_comp
             {P : poly_code}
             {x y : one_type}
             (f : x → y)
             (a : PA₀ P x)
    : (pr1 (pr111 (poly_path_groupoid P) y))
        (PA₁ P f (pr1 (poly_path_groupoid P x) a))
      =
      pr1 (poly_path_groupoid P y) (PA₁ P f a)
    := ap (λ z, pr1 ((pr111 (poly_path_groupoid P)) y) (PA₁ P f z))
          (poly_path_groupoid_is_id a).

  Definition poly_path_groupoid_gquot_counit_map_po
             {P : poly_code}
             {x y : one_type}
             (f : x → y)
             {a₁ a₂ : PA₀ P x}
             (g : poly_act_groupoid P (one_type_to_groupoid x) ⟦ a₁, a₂ ⟧)
    : @PathOver
        _
        (gcl (poly_act_groupoid P (one_type_to_groupoid x)) a₁)
        (gcl (poly_act_groupoid P (one_type_to_groupoid x)) a₂)
        (λ z,
         pr1 (pr111 (poly_path_groupoid P) y)
             (PA₁ P f
                  (gquot_counit_map
                     (make_one_type (PA₀ P x) (poly_act_hlevel P x))
                     (GQ₁ ((poly_path_groupoid P) x)
                          z)))
         =
         gquot_counit_map
           (make_one_type (PA₀ P y) (poly_act_hlevel P y))
           (GQ₁ ((poly_path_groupoid P) y)
                (GQ₁
                   (poly_act_functor
                      P (one_type_to_groupoid x) (one_type_to_groupoid y)
                      (function_to_functor f))
                   z)))
        (poly_path_groupoid_gquot_counit_map_comp f a₁)
        (poly_path_groupoid_gquot_counit_map_comp f a₂)
        (gcleq (poly_act_groupoid P (one_type_to_groupoid x)) g).
  Proof.
    use map_PathOver.
    refine (whisker_square
              idpath
              _
              _
              idpath
              _).
    - refine (!_).
      etrans.
      {
        refine (!_).
        exact (maponpathscomp _ _ (gcleq _ g)).
      }
      apply ap.
      etrans.
      {
        refine (!_).
        exact (maponpathscomp _ _ (gcleq _ g)).
      }
      apply ap.
      etrans.
      {
        refine (!_).
        exact (maponpathscomp _ _ (gcleq _ g)).
      }
      etrans.
      {
        apply ap.
        apply gquot_rec_beta_gcleq.
      }
      apply gquot_rec_beta_gcleq.
    - refine (!_).
      etrans.
      {
        refine (!_).
        exact (maponpathscomp _ _ (gcleq _ g)).
      }
      etrans.
      {
        apply ap.
        etrans.
        {
          refine (!_).
          exact (maponpathscomp _ _ (gcleq _ g)).
        }
        etrans.
        {
          apply ap.
          apply gquot_rec_beta_gcleq.
        }
        apply gquot_rec_beta_gcleq.
      }
      apply gquot_rec_beta_gcleq.
    - unfold square.
      induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
      + induction g.
        exact (@idpath _ idpath).
      + induction g.
        exact (@idpath _ idpath).
      + induction a₁ as [a₁ | a₁], a₂ as [a₂ | a₂].
        * etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                exact (maponpathscomp
                         inl
                         (coprodf (PA₁ P₁ f) (PA₁ P₂ f))
                         (# (pr1 ((poly_path_groupoid P₁) x)) g)).
              }
              exact (!(maponpathscomp
                         (PA₁ P₁ f)
                         inl
                         (# (pr1 ((poly_path_groupoid P₁) x)) g))).
            }
            etrans.
            {
              exact (maponpathscomp
                       inl
                       (pr1 (pr111 (poly_path_groupoid (P₁ + P₂)) y))
                       (ap (PA₁ P₁ f)
                           (# (pr1 ((poly_path_groupoid P₁) x)) g))).
            }
            exact (!(maponpathscomp
                       (pr1 (pr111 (poly_path_groupoid P₁) y))
                       inl
                       (ap (PA₁ P₁ f)
                           (# (pr1 ((poly_path_groupoid P₁) x)) g)))).
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              exact (maponpathscomp
                       inl
                       _
                       (poly_path_groupoid_is_id a₂)).
            }
            exact (!(maponpathscomp
                       (λ z, pr1 ((pr111 (poly_path_groupoid P₁)) y) (PA₁ P₁ f z))
                       inl
                       (poly_path_groupoid_is_id a₂))).
          }
          etrans.
          {
            refine (!_).
            apply (maponpathscomp0 inl).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              exact (maponpathscomp
                       inl
                       _
                       (poly_path_groupoid_is_id a₁)).
            }
            exact (!(maponpathscomp
                       (λ z, pr1 ((pr111 (poly_path_groupoid P₁)) y) (PA₁ P₁ f z))
                       inl
                       (poly_path_groupoid_is_id a₁))).
          }
          etrans.
          {
            refine (!_).
            apply (maponpathscomp0 inl).
          }
          apply ap.
          exact (!(IHP₁ a₁ a₂ g)).
        * exact (fromempty g).
        * exact (fromempty g).
        * etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                exact (maponpathscomp
                         inr
                         (coprodf (PA₁ P₁ f) (PA₁ P₂ f))
                         (# (pr1 ((poly_path_groupoid P₂) x)) g)).
              }
              exact (!(maponpathscomp
                         (PA₁ P₂ f)
                         inr
                         (# (pr1 ((poly_path_groupoid P₂) x)) g))).
            }
            etrans.
            {
              exact (maponpathscomp
                       inr
                       (pr1 (pr111 (poly_path_groupoid (P₁ + P₂)) y))
                       (ap (PA₁ P₂ f)
                           (# (pr1 ((poly_path_groupoid P₂) x)) g))).
            }
            exact (!(maponpathscomp
                       (pr1 (pr111 (poly_path_groupoid P₂) y))
                       inr
                       (ap (PA₁ P₂ f)
                           (# (pr1 ((poly_path_groupoid P₂) x)) g)))).
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              exact (maponpathscomp
                       inr
                       _
                       (poly_path_groupoid_is_id a₂)).
            }
            exact (!(maponpathscomp
                       (λ z, pr1 ((pr111 (poly_path_groupoid P₂)) y) (PA₁ P₂ f z))
                       inr
                       (poly_path_groupoid_is_id a₂))).
          }
          etrans.
          {
            refine (!_).
            apply (maponpathscomp0 inr).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              exact (maponpathscomp
                       inr
                       _
                       (poly_path_groupoid_is_id a₁)).
            }
            exact (!(maponpathscomp
                       (λ z, pr1 ((pr111 (poly_path_groupoid P₂)) y) (PA₁ P₂ f z))
                       inr
                       (poly_path_groupoid_is_id a₁))).
          }
          etrans.
          {
            refine (!_).
            apply (maponpathscomp0 inr).
          }
          apply ap.
          exact (!(IHP₂ a₁ a₂ g)).
      + specialize (IHP₁ (pr1 a₁) (pr1 a₂) (pr1 g)).
        specialize (IHP₂ (pr2 a₁) (pr2 a₂) (pr2 g)).
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply ap.
            exact (!(maponpaths_pathsdirprod
                       (PA₁ P₁ f)
                       (PA₁ P₂ f)
                       (# (pr1 ((poly_path_groupoid P₁) x)) (pr1 g))
                       (# (pr1 ((poly_path_groupoid P₂) x)) (pr2 g)))).
          }
          exact (!(maponpaths_pathsdirprod
                     (pr1 (poly_path_groupoid P₁ y))
                     (pr1 (poly_path_groupoid P₂ y))
                     _
                     _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (!(maponpaths_pathsdirprod
                     (λ z, pr1 (poly_path_groupoid P₁ y) (PA₁ P₁ f z))
                     (λ z, pr1 (poly_path_groupoid P₂ y) (PA₁ P₂ f z))
                     (poly_path_groupoid_is_id (pr1 a₂))
                     (poly_path_groupoid_is_id (pr2 a₂)))).
        }
        refine (pathsdirprod_concat _ _ _ _ @ _).
        refine (ap (λ z, pathsdirprod z _) IHP₁ @ _).
        refine (ap (pathsdirprod _) IHP₂ @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(maponpaths_pathsdirprod
                     (λ z, pr1 (poly_path_groupoid P₁ y) (PA₁ P₁ f z))
                     (λ z, pr1 (poly_path_groupoid P₂ y) (PA₁ P₂ f z))
                     (poly_path_groupoid_is_id (pr1 a₁))
                     (poly_path_groupoid_is_id (pr2 a₁)))).
        }
        apply pathsdirprod_concat.
  Qed.
    
  Definition poly_path_groupoid_gquot_counit_map
             {P : poly_code}
             {x y : one_type}
             (f : x → y)
    : ∏ (z : gquot (poly_act_groupoid P (one_type_to_groupoid x))),
      pr1 (pr111 (poly_path_groupoid P) y)
          (PA₁ P f
               (gquot_counit_map
                  (make_one_type (PA₀ P x) (poly_act_hlevel P x))
                  (GQ₁ ((poly_path_groupoid P) x)
                       z)))
      =
      gquot_counit_map
        (make_one_type (PA₀ P y) (poly_act_hlevel P y))
        (GQ₁ ((poly_path_groupoid P) y)
             (GQ₁
                (poly_act_functor
                   P (one_type_to_groupoid x) (one_type_to_groupoid y)
                   (function_to_functor f))
                z)).
  Proof.
    use gquot_ind_set.
    - exact (poly_path_groupoid_gquot_counit_map_comp f).
    - exact (@poly_path_groupoid_gquot_counit_map_po _ _ _ f).
    - intro.
      exact (poly_act_hlevel P y _ _).
  Defined.


  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₁
             {P : poly_code}
             {X Y : one_type}
             (f : X → Y)
             (z : PA₀ P (gquot (one_type_to_groupoid X)))
    : (poly_comp P (gquot_counit_map X) f z)
        @ poly_homot P (gquot_counit_naturality f) z
      =
      (PA₁_gquot_counit_map f z)
        @ poly_comp P (GQ₁ (function_to_functor f)) (gquot_counit_map Y) z.
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact idpath.
    - revert z.
      use gquot_ind_prop.
      + intro ; exact idpath.
      + intro.
        exact (one_type_isofhlevel Y _ _ _ _).
    - induction z as [z | z].
      + refine (!(maponpathscomp0 inl _ _) @ _ @ maponpathscomp0 inl _ _).
        exact (ap (ap inl) (IHP₁ z)).
      + refine (!(maponpathscomp0 inr _ _) @ _ @ maponpathscomp0 inr _ _).
        exact (ap (ap inr) (IHP₂ z)).
    - refine (pathsdirprod_concat _ _ _ _ @ _ @ !(pathsdirprod_concat _ _ _ _)).
      refine (ap (λ z, pathsdirprod z _) (IHP₁ (pr1 z)) @ _).
      exact (ap (pathsdirprod _) (IHP₂ (pr2 z))).
  Qed.

  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₂
             {P : poly_code}
             {X Y : one_type}
             (f : X → Y)
             (z : PA₀ P X)
    : ap (PA₁ P f) (poly_path_groupoid_is_id z)
      =
      (pr11 (psnaturality_of (poly_path_groupoid P) f) z)
        @ poly_path_groupoid_is_id (PA₁ P f z).
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (@idpath _ idpath).
    - exact (@idpath _ idpath).
    - induction z as [z | z].
      + refine (maponpathscomp
                  inl
                  (coprodf (PA₁ P₁ f) (PA₁ P₂ f))
                  (poly_path_groupoid_is_id z)
                @ _).
        refine (!(maponpathscomp (PA₁ P₁ f) inl (poly_path_groupoid_is_id z)) @ _).
        exact (ap (ap inl) (IHP₁ z) @ maponpathscomp0 inl _ _).
      + refine (maponpathscomp
                  inr
                  (coprodf (PA₁ P₁ f) (PA₁ P₂ f))
                  (poly_path_groupoid_is_id z) @ _).
        refine (!(maponpathscomp (PA₁ P₂ f) inr (poly_path_groupoid_is_id z)) @ _).
        exact (ap (ap inr) (IHP₂ z) @ maponpathscomp0 inr _ _).
    - refine (!(maponpaths_pathsdirprod
                  (PA₁ P₁ f)
                  (PA₁ P₂ f)
                  (poly_path_groupoid_is_id (pr1 z))
                  (poly_path_groupoid_is_id (pr2 z)))
               @ _).
      refine (_ @ !(pathsdirprod_concat
                      ((pr11 (psnaturality_of (poly_path_groupoid P₁) f)) (pr1 z))
                      _
                      ((pr11 (psnaturality_of (poly_path_groupoid P₂) f)) (pr2 z))
                      _)).
      exact (ap (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
                @ ap (pathsdirprod _) (IHP₂ (pr2 z))).
  Qed.

  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₃
             {P : poly_code}
             {x y : one_types}
             {f : one_types ⟦ x, y ⟧}
             {xx : (disp_alg_bicat (⟦ P ⟧)) x}
             {yy : (disp_alg_bicat (⟦ P ⟧)) y}
             (ff : xx -->[ f] yy)
             (z : PA₀ P (gquot (one_type_to_groupoid x)))
    : pr1 ff (PA₁ P (gquot_counit_map x) z)
          @ ap yy (PA₁_gquot_counit_map f z)
      =
      ap f (ap xx (!(poly_path_groupoid_is_id _)))
         @ pr1 ff ((pr1 ((poly_path_groupoid P) x)) (PA₁ P (gquot_counit_map x) z))
         @ ap yy ((pr11 (psnaturality_of (poly_path_groupoid P) f) _)
                    @ poly_path_groupoid_is_id
                        (PA₁ P f (PA₁ P (gquot_counit_map x) z))
                    @ PA₁_gquot_counit_map f z).
  Proof.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply path_assoc.
      }
      apply (maponpathscomp0 yy).
    }
    do 2 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (!_).
    refine (homotsec_natural
              (λ z, pr1 ff z)
              (poly_path_groupoid_is_id (PA₁ P (gquot_counit_map x) z))
            @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp
                 xx f
                 (!(poly_path_groupoid_is_id (PA₁ P (gquot_counit_map x) z))))).
    }
    refine (_ @ path_assoc _ _ _).
    do 2 apply maponpaths.
    refine (!(maponpathscomp _ yy _) @ _).
    apply maponpaths.
    apply (algebra_biadjunction_lift_counit_pstrans_nat_lem_help₂ f).
  Qed.
  
  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₄
             {P : poly_code}
             {x y : one_types}
             {f : one_types ⟦ x, y ⟧}
             {xx : (disp_alg_bicat (⟦ P ⟧)) x}
             {yy : (disp_alg_bicat (⟦ P ⟧)) y}
             (na : ((poly_path_groupoid
                       P x
                       ∙ function_to_functor xx)
                      ∙ function_to_functor f)
                     ⟹
                     (poly_act_functor
                        P _ _ (function_to_functor f)
                        ∙ (poly_path_groupoid P y ∙ function_to_functor yy)))
    : ∏ (z : gquot (poly_act_groupoid P (one_type_to_groupoid x))),
      ap f
           (gquot_counit_naturality
              xx
              (GQ₁ ((poly_path_groupoid P) x)
                   z)
              @ ap (gquot_counit_map x)
              (GQC ((poly_path_groupoid P) x) (function_to_functor xx)
                   z))
        @ gquot_counit_naturality
            f
            (GQ₁ ((poly_path_groupoid P) x ∙ function_to_functor xx)
                 z)
        @ ap (gquot_counit_map y)
             (((GQC
                  ((poly_path_groupoid P) x ∙ function_to_functor xx)
                  (function_to_functor f)
                  z
             @ GQ₂ na z)
             @ ! GQC
                   (poly_act_functor
                      P
                      (one_type_to_groupoid x) (one_type_to_groupoid y)
                      (function_to_functor f))
                   ((poly_path_groupoid P) y ∙ function_to_functor yy)
                   z)
             @ ! GQC ((poly_path_groupoid P) y) (function_to_functor yy)
                   (GQ₁
                      (poly_act_functor
                         P
                         (one_type_to_groupoid x) (one_type_to_groupoid y)
                         (function_to_functor f))
                      z))
             @ ! gquot_counit_naturality yy
                   (GQ₁ ((poly_path_groupoid P) y)
                        (GQ₁
                           (poly_act_functor
                              P
                              (one_type_to_groupoid x) (one_type_to_groupoid y)
                              (function_to_functor f))
                           z))
        =
        algebra_biadjunction_lift_counit_pstrans_GQ_nat f na z.
  Proof.
    use gquot_ind_prop.
    - intros a.
      refine (pathscomp0rid _ @ ap _ (pathscomp0rid _ @ pathscomp0rid _) @ _).
      exact (gquot_rec_beta_gcleq
               (one_type_to_groupoid y)
               _ _ _ _ _ _ _ _ _).
    - intro.
      exact (one_type_isofhlevel y _ _ _ _).
  Qed.

  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₅
             {P : poly_code}
             {x y : one_types}
             {f : one_types ⟦ x, y ⟧}
             (yy : (disp_alg_bicat (⟦ P ⟧)) y)
             (z : PA₀ P (gquot (one_type_to_groupoid x)))
    : ap (GQ₁ ((poly_path_groupoid P) y ∙ function_to_functor yy))
         (pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z)
    @ ! GQC ((poly_path_groupoid P) y) (function_to_functor yy)
            (poly_gquot P
               (one_type_to_groupoid y)
               (PA₁ P (GQ₁ (function_to_functor f)) z))
    =
    ! GQC ((poly_path_groupoid P) y) (function_to_functor yy)
          ((poly_gquot
              P (one_type_to_groupoid x)
              · GQ₁
                  (poly_act_functor
                     P (one_type_to_groupoid x) (one_type_to_groupoid y)
                     (function_to_functor f))) z)
    @ ap (GQ₁ (function_to_functor yy))
         (ap (GQ₁ ((poly_path_groupoid P) y))
             (pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z)).
  Proof.
    pose (homotsec_natural
            (invhomot (GQC ((poly_path_groupoid P) y) (function_to_functor yy)))
            (pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z))
      as p.
    unfold invhomot in p.
    etrans.
    {
      apply maponpaths.
      exact p.
    }
    do 2 refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply maponpathscomp.
    }
    apply maponpaths_2.
    refine (_ @ pathscomp0lid _).
    apply maponpaths_2.
    refine (!(maponpathscomp0 _ _ _) @ _).
    etrans.
    {
      apply ap.
      apply pathsinv0r.
    }
    apply idpath.
  Qed.

  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₆
             {P : poly_code}
             {x y : one_types}
             {f : one_types ⟦ x, y ⟧}
             (yy : (disp_alg_bicat (⟦ P ⟧)) y)
             (z : PA₀ P (gquot (one_type_to_groupoid x)))
    : ap (gquot_counit_map y)
         (ap (GQ₁ (function_to_functor yy))
             (ap (GQ₁ ((poly_path_groupoid P) y))
                 (pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z)))
    @ ! gquot_counit_naturality yy
          (GQ₁ ((poly_path_groupoid P) y)
               ((poly_gquot P) (one_type_to_groupoid y)
                               (PA₁ P (GQ₁ (function_to_functor f)) z)))
    =
    ! gquot_counit_naturality yy
        _
    @ ap yy
         (ap (gquot_counit_map _)
             (ap (GQ₁ _)
                 (pr1 (psnaturality_of
                         (poly_gquot P)
                         (function_to_functor f)) z))).
  Proof.
    pose (homotsec_natural
             (invhomot (gquot_counit_naturality yy))
             (ap (GQ₁ (poly_path_groupoid P y))
                 (pr1 (psnaturality_of
                         (poly_gquot P)
                         (function_to_functor f)) z)))
      as p.
    unfold invhomot in p.
    etrans.
    {
      apply maponpaths.
      exact p.
    }
    refine (!_).    
    etrans.
    {
      apply maponpaths.
      exact (maponpathscomp
               (gquot_counit_map ((⟦ P ⟧) y))
               yy
               (ap (GQ₁ ((poly_path_groupoid P) y))
                   (pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z))).
    }
    do 2 refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    refine (!(pathscomp0lid _) @ _).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp.
      }
      refine (!(maponpathscomp0 _ _ _) @ _).
      apply ap.
      apply pathsinv0r.
    }
    apply idpath.
  Qed.

  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₇
             {P : poly_code}
             {x y : one_types}
             {f : one_types ⟦ x, y ⟧}
             {xx : (disp_alg_bicat (⟦ P ⟧)) x}
             {yy : (disp_alg_bicat (⟦ P ⟧)) y}
             (na : ((poly_path_groupoid P x
                      ∙ function_to_functor xx)
                    ∙ function_to_functor f)
                   ⟹
                   (poly_act_functor P _ _ (function_to_functor f)
                    ∙ (poly_path_groupoid P y ∙ function_to_functor yy)))
    : ∏ (z : gquot (poly_act_groupoid P (one_type_to_groupoid x))),
    algebra_biadjunction_lift_counit_pstrans_GQ_nat
        f na
        z
    =
    ap f
       (ap xx
           (! poly_path_groupoid_is_id
              (gquot_counit_map
                 (make_one_type (PA₀ P _) (poly_act_hlevel P x))
                 (GQ₁ ((poly_path_groupoid P) x) z))))
    @ na
        (gquot_counit_map
           (make_one_type (PA₀ P _) (poly_act_hlevel P x))
           (GQ₁ (poly_path_groupoid P x) z))
    @ ap yy
         (poly_path_groupoid_gquot_counit_map
            f z).
  Proof.
    use gquot_ind_prop.
    - intros a ; simpl.
      refine (homotsec_natural (λ z, na z) (poly_path_groupoid_is_id a) @ _).
      refine (!_).
      simpl.
      unfold poly_path_groupoid_gquot_counit_map_comp.
      etrans.
      {
        do 2 apply maponpaths.
        exact (maponpathscomp
                 (λ z, (pr1 ((pr111 (poly_path_groupoid P)) y)) (PA₁ P f z))
                 yy
                 (poly_path_groupoid_is_id a)).
      }
      refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
      do 2 apply maponpaths_2.
      refine (!_).
      refine (!(maponpathscomp _ _ _) @ _).
      apply maponpaths.
      refine (!(maponpathscomp _ _ _) @ _).
      apply maponpaths.
      clear na. clear yy. clear xx.
      induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
      + apply idpath.
      + apply idpath.
      + induction a as [a | a].
        * clear IHP₂. specialize (IHP₁ a).
          refine (_ @ maponpathsinv0
                        inl
                        (poly_path_groupoid_is_id
                           ((pr1 ((poly_path_groupoid P₁) x)) a))).
          refine (_ @ maponpaths (ap inl) IHP₁).
          etrans.
          {
            etrans.
            {
              apply ap.
              exact (!(maponpathsinv0 inl (poly_path_groupoid_is_id a))).
            }
            exact (maponpathscomp
                      inl
                      (pr1 ((pr111 (poly_path_groupoid (P₁ + P₂))) x))
                      _).
          }
          exact (!(maponpathscomp
                        _
                        inl
                        _)).
        * clear IHP₁. specialize (IHP₂ a).
          refine (_ @ maponpathsinv0
                        inr
                        (poly_path_groupoid_is_id
                           ((pr1 ((poly_path_groupoid P₂) x)) a))).
          refine (_ @ maponpaths (ap inr) IHP₂).
          etrans.
          {
            etrans.
            {
              apply ap.
              exact (!(maponpathsinv0 inr (poly_path_groupoid_is_id a))).
            }
            exact (maponpathscomp
                      inr
                      (pr1 ((pr111 (poly_path_groupoid (P₁ + P₂))) x))
                      _).
          }
          exact (!(maponpathscomp
                        _
                        inr
                        _)).
      + simpl.
        refine (_ @ !(pathsdirprod_inv _ _)).
        etrans.
        {
          apply ap.
          apply pathsdirprod_inv.
        }
        etrans.
        {
          exact (!(maponpaths_pathsdirprod
                   (λ z, pr1 ((poly_path_groupoid P₁) x) z)
                   (λ z, pr1 ((poly_path_groupoid P₂) x) z)
                   _
                   _)).
        }        
        refine (ap (λ z, pathsdirprod z _) (IHP₁ (pr1 a)) @ _).
        exact (ap (pathsdirprod _) (IHP₂ (pr2 a))).
    - intro.
      exact (one_type_isofhlevel _ _ _ _ _).
  Qed.
    
  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₈
             {P : poly_code}
             {x y : one_types}
             {f : one_types ⟦ x, y ⟧}
             {xx : (disp_alg_bicat (⟦ P ⟧)) x}
             {yy : (disp_alg_bicat (⟦ P ⟧)) y}
             (z : PA₀ P (gquot (one_type_to_groupoid x)))
             (na : ((poly_path_groupoid P x
                      ∙ function_to_functor xx)
                    ∙ function_to_functor f)
                   ⟹
                   (poly_act_functor P _ _ (function_to_functor f)
                    ∙ (poly_path_groupoid P y ∙ function_to_functor yy)))
    : ap f (ap xx (! εε_comp P z)) @
         (algebra_biadjunction_lift_counit_pstrans_GQ_nat
            f na ((poly_gquot P) (one_type_to_groupoid x) z))
    =
    ap f (ap xx (! poly_path_groupoid_is_id (PA₁ P (gquot_counit_map x) z)))
    @ na _
    @ ap yy
        (ap _ (ap _ (!(εε_comp P z)))
            @ poly_path_groupoid_gquot_counit_map _ _).
  Proof.
    induction (εε_comp P z).
    exact (algebra_biadjunction_lift_counit_pstrans_nat_lem_help₇
             na
             (poly_gquot P (one_type_to_groupoid x) z)).
  Qed.



  Definition test
             {P : poly_code}
             {x y : one_types}
             (f : one_types ⟦ x, y ⟧)
             (z : PA₀ P (gquot (one_type_to_groupoid x)))
    : poly_path_groupoid_gquot_counit_map
        f
        (poly_gquot P (one_type_to_groupoid x) z)
    @ ap (gquot_counit_map ((⟦ P ⟧) y))
         (ap (GQ₁ ((poly_path_groupoid P) y))
             (pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z))
    @ εε_comp P (PA₁ P (GQ₁ (function_to_functor f)) z)
    =
    poly_path_groupoid_is_id _
    @ ap (PA₁ P f) (εε_comp P z)
    @ PA₁_gquot_counit_map f z.
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (@idpath _ (@idpath _ z)).
    - revert z.
      use gquot_ind_prop.
      + intros a.
        apply idpath.
      + intro ; exact (one_type_isofhlevel _ _ _ _ _).
    - induction z as [z | z].
      + clear IHP₂ ; specialize (IHP₁ z).
        apply TODO.
      + clear IHP₁ ; specialize (IHP₂ z).
        apply TODO.
    - apply TODO.
  Qed.
  
  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem_help₉
             {P : poly_code}
             {x y : one_types}
             (f : one_types ⟦ x, y ⟧)
             (z : PA₀ P (gquot (one_type_to_groupoid x)))
    : (ap (pr1 ((pr111 (poly_path_groupoid P)) y))
          (ap (PA₁ P f) (! εε_comp P z))
    @ poly_path_groupoid_gquot_counit_map f
              (poly_gquot P (one_type_to_groupoid x) z))
    @ ap (gquot_counit_map ((⟦ P ⟧) y))
         (ap (GQ₁ ((poly_path_groupoid P) y))
             (pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z))
    @ εε_comp P (PA₁ P (GQ₁ (function_to_functor f)) z)
    =
    poly_path_groupoid_is_id
      (PA₁ P f (PA₁ P (gquot_counit_map x) z))
    @ PA₁_gquot_counit_map f z.
  Proof.
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      apply test.
    }
    do 2 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    pose (homotsec_natural (λ z, poly_path_groupoid_is_id (PA₁ P f z)) (εε_comp P z))
      as p.
    simpl in p.
    refine (!(path_assoc _ _ _) @ _ @ !p).
    apply maponpaths_2.
    apply maponpathscomp.
  Qed.

  Definition algebra_biadjunction_lift_counit_pstrans_nat_lem
             {P : poly_code}
             {x y : one_types}
             {f : one_types ⟦ x, y ⟧}
             {xx : (disp_alg_bicat (⟦ P ⟧)) x}
             {yy : (disp_alg_bicat (⟦ P ⟧)) y}
             (ff : xx -->[ f] yy)
             (z : PA₀ P (gquot (one_type_to_groupoid x)))
             (na : ((poly_path_groupoid P x
                      ∙ function_to_functor xx)
                    ∙ function_to_functor f)
                     ⟹
                     (poly_act_functor P _ _ (function_to_functor f)
                       ∙ (poly_path_groupoid P y ∙ function_to_functor yy)))
             (H : ∏ (q : PA₀ P (x : one_type)),
                  na q
                  =
                  pr1 ff (pr1 (poly_path_groupoid P x) q)
                      @ ap yy (pr11 (psnaturality_of (poly_path_groupoid P) f) q))
    : pr1 ff (PA₁ P (gquot_counit_map x) z)
     @ ap yy (PA₁_gquot_counit_map f z)
     =
     ap f
        (ap xx (!(εε_comp P z))
         @ gquot_counit_naturality
             xx
             (GQ₁
                (poly_path_groupoid P x)
                (poly_gquot P (one_type_to_groupoid x) z))
         @ ap (gquot_counit_map x) (GQC _ _ _))
     @ gquot_counit_naturality
         f
         (GQ₁ (poly_path_groupoid P x ∙ function_to_functor xx)
              (poly_gquot P (one_type_to_groupoid x) z))
     @ ap (gquot_counit_map y)
          (GQC _ _ _
            @ GQ₂ na _
            @ !(GQC _ _ _)
            @ ap (GQ₁ ((poly_path_groupoid P) y ∙ function_to_functor yy))
                 (pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z))
      @ ap (gquot_counit_map y) (! GQC _ _ _)
      @ ! gquot_counit_naturality
            yy
            (GQ₁ (poly_path_groupoid P y)
                 (poly_gquot
                    P (one_type_to_groupoid y)
                    (PA₁ P (GQ₁ (function_to_functor f)) z)))
      @ ap yy (εε_comp P (PA₁ P (GQ₁ (function_to_functor f)) z)).
  Proof.
    etrans.
    {
      apply algebra_biadjunction_lift_counit_pstrans_nat_lem_help₃.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        exact (!(maponpathscomp0 (gquot_counit_map y) _ _)).
      }
      etrans.
      {
        apply maponpaths.
        do 3 refine (!path_assoc _ _ _ @ ap _ _).
        exact (algebra_biadjunction_lift_counit_pstrans_nat_lem_help₅ yy z).
      }
      etrans.
      {
        apply maponpaths.
        refine (path_assoc _ _ _ @ path_assoc _ _ _ @ _).
        apply path_assoc.
      }
      apply (maponpathscomp0 (gquot_counit_map y)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (algebra_biadjunction_lift_counit_pstrans_nat_lem_help₆ yy z).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      do 3 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      do 2 refine (!(path_assoc _ _ _) @ _).
      exact (algebra_biadjunction_lift_counit_pstrans_nat_lem_help₄
               na ((poly_gquot P) (one_type_to_groupoid x) z)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply (maponpathscomp0 yy).
      }
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (!(H (PA₁ P (gquot_counit_map x) z))).
    }
    clear H ff.
    refine (!_).
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (algebra_biadjunction_lift_counit_pstrans_nat_lem_help₈ z na).
    }
    do 2 refine (!(path_assoc _ _ _) @ _).
    apply ap.
    refine (!(path_assoc _ _ _) @ _).
    apply ap.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (maponpathscomp0 yy).
      }
      refine (!_).
      apply (maponpathscomp0 yy).
    }
    apply ap.
    exact (algebra_biadjunction_lift_counit_pstrans_nat_lem_help₉ f z).
  Qed.

  Definition algebra_biadjunction_lift_counit_pstrans_nat
             (P : poly_code)
    : algebra_lift_pstrans_nat
        (counit_of_lifted_biadj
           gquot_biadj_data (poly_gquot P) (poly_path_groupoid P)
           (εε P)).
  Proof.
    intros x y f xx yy ff.
    use funextsec.
    intro z.
    (*




  simpl.
  cbn.
  unfold homotcomp, invhomot, funhomotsec, homotfun.
  cbn.
  simpl in z.

  refine (!_).
  etrans.
  {
    refine (ap (λ z, (z @ _) @ _) _).
    refine (pathscomp0rid _ @ _).
    refine (ap (λ z, z @ _) _).
    refine (pathscomp0rid _ @ _).
    refine (ap (λ z, ap f z) _).
    refine (ap (λ q, q @ ap xx (εε_comp P z)) _).
    refine (pathscomp0rid _ @ _).
    apply pathscomp0rid.
  }
  etrans.
  {
    refine (!(path_assoc _ _ _) @ ap (λ z, _ @ z) _).
    exact (!(maponpathscomp0
               yy
               (poly_comp P (gquot_counit_map x) f z)
               (poly_homot P (gquot_counit_naturality f) z))).
  }
  etrans.
  {
    do 2 apply maponpaths.
    apply algebra_biadjunction_lift_counit_pstrans_nat_lem_help₁.
  }
  

  

  simpl.
  cbn.
  unfold homotcomp, funhomotsec, invhomot, homotfun.
  cbn.
     *)
    apply TODO.
  Qed.
End CounitNat.
