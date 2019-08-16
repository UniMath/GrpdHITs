Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBiadjunction.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.
Require Import biadjunctions.all.
Require Import hit_biadjunction.hit_prealgebra_biadj.biadj_data.

Local Open Scope cat.

(** The naturality condition for the pseudotransformations *)
Local Definition TODO {A : UU} : A.
Admitted.

(** Lemmata *)
Section LiftUnitHelp.
  Local Arguments idpath {_ _}.
  Local Notation "'ap'" := maponpaths.
  Local Notation "'GQ₀'" := gquot_functor_obj.
  Local Notation "'GQ₁'" := gquot_functor_map.
  Local Notation "'GQ₂'" := gquot_functor_cell.
  Local Notation "'GQC'" := gquot_functor_composition.
  Local Notation "'PA₀'" := poly_act.
  Local Notation "'PA₁'" := poly_map.
  Local Notation "'PA₂'" := poly_act_nat_trans_data.
  Local Notation "'PAC'" := poly_act_functor_composition_data.
  
  Definition lift_unit_pstrans
             (P : poly_code)
             (x y : groupoid)
             (f : x ⟶ y)
             (z : poly_act P (pr1 x))
  : PA₁ P (GQ₁ f) (pr1 ((poly_path_groupoid P) (GQ₀ x)) (PA₁ P (gcl x) z))
    =
    pr1 ((poly_path_groupoid P) (GQ₀ y)) (PA₁ P (gcl y) (PA₁ P f z)).
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact idpath.
    - exact idpath.
    - induction z as [z | z].
      + exact (maponpaths inl (IHP₁ z)).
      + exact (maponpaths inr (IHP₂ z)).
    - apply pathsdirprod.
      + exact (IHP₁ (pr1 z)).
      + exact (IHP₂ (pr2 z)).
  Defined.    

  Definition lift_unit_pstrans_eq
             {P : poly_code}
             {x y : groupoid}
             (f : x ⟶ y)
             (z : poly_act P (pr1 x))
    : pr11
        (psnaturality_of (poly_path_groupoid P) (GQ₁ f))
        (PA₁ P (gcl x) z)
    @ # (pr1 ((poly_path_groupoid P) (GQ₀ y)))
          (poly_act_functor_composition_data
             P x (one_type_to_groupoid (gquot_functor_obj x))
             (one_type_to_groupoid (gquot_functor_obj y)) (gquot_unit_functor x)
             (function_to_functor (gquot_functor_map f)) z)
    @ # (pr1 ((poly_path_groupoid P) (gquot_functor_obj y)))
          (poly_act_nat_trans_data
             P x (one_type_to_groupoid (gquot_functor_obj y))
             (gquot_unit_functor x ∙ function_to_functor (gquot_functor_map f))
             (f ∙ gquot_unit_functor y) (gquot_unit_nat_trans x y f) z)
    =
    lift_unit_pstrans P x y f z
    @ # (pr1 ((poly_path_groupoid P) (gquot_functor_obj y)))
           (poly_act_functor_composition_data
              P x y (one_type_to_groupoid (gquot_functor_obj y)) f
              (gquot_unit_functor y) z).
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (@idpath _ (@idpath _ z)).
    - apply idpath.
    - induction z as [z | z].
      + simpl.
        refine (_ @ maponpathscomp0 _ _ _).
        refine (maponpaths (λ z, _ @ z) (!(maponpathscomp0 _ _ _)) @ _).
        refine (!(maponpathscomp0 _ _ _) @ _).
        apply maponpaths.
        apply (IHP₁ z).
      + simpl.
        refine (_ @ maponpathscomp0 _ _ _).
        refine (maponpaths (λ z, _ @ z) (!(maponpathscomp0 _ _ _)) @ _).
        refine (!(maponpathscomp0 _ _ _) @ _).
        apply maponpaths.
        apply (IHP₂ z).
    - simpl.
      refine (_ @ !(pathsdirprod_concat _ _ _ _)).
      refine (maponpaths (λ z, _ @ z) (pathsdirprod_concat _ _ _ _) @ _).
      refine (pathsdirprod_concat _ _ _ _ @ _).
      etrans.
      {
        exact (maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))).
      }
      exact (maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
  Qed.

  Local Definition lift_unit_help₁
        (P : poly_code)
        {x y : groupoid}
        (f : x ⟶ y)
        (xx : (⦃ P ⦄ x : groupoid) ⟶ x)
        (z : poly_act P (pr1 x))
    : ap
        (GQ₁ f ∘ GQ₁ xx)%functions (ηη_comp P z)
    @ GQC
        xx f
        ((poly_gquot P) x ((pr1 ((poly_path_groupoid P) (GQ₀ x)))
                             (PA₁ P (gcl x) z)))
      =
      ap (GQ₁ (xx ∙ f)) (ηη_comp P z).
  Proof.
    induction (ηη_comp P z).
    apply idpath.
  Qed.

  Local Definition lift_unit_help₂
        (P : poly_code)
        {x y : groupoid}
        {f : x ⟶ y}
        {xx : (⦃ P ⦄ x : groupoid) ⟶ x}
        {yy : (⦃ P ⦄ y : groupoid) ⟶ y}
        (ff : xx ∙ f ⟹ # ⦃ P ⦄ f ∙ yy)
        (z : poly_act P (pr1 x))
    : ap (GQ₁ (xx ∙ f)) (ηη_comp P z)
    @ GQ₂ ff ((poly_gquot P) x ((pr1 ((poly_path_groupoid P) (GQ₀ x))) (PA₁ P (gcl x) z)))
    =
    gcleq y (pr1 ff z) @ ap (GQ₁ (poly_act_functor P x y f ∙ yy)) (ηη_comp P z).
  Proof.
    induction (ηη_comp P z).
    exact (!(pathscomp0rid _)).
  Qed.
  
  Local Definition lift_unit_help₃
        (P : poly_code)
        {x y : groupoid}
        {f : x ⟶ y}
        {xx : (⦃ P ⦄ x : groupoid) ⟶ x}
        {yy : (⦃ P ⦄ y : groupoid) ⟶ y}
        (ff : xx ∙ f ⟹ # ⦃ P ⦄ f ∙ yy)
        (z : poly_act P (pr1 x))
    : ap (GQ₁ (poly_act_functor P x y f ∙ yy)) (ηη_comp P z)
    @ ! GQC (poly_act_functor P x y f) yy
            ((poly_gquot P) x ((pr1 ((poly_path_groupoid P) (GQ₀ x))) (PA₁ P (gcl x) z)))
    = ap (GQ₁ yy) (ap (GQ₁ (poly_act_functor P x y f)) (ηη_comp P z)).
  Proof.
    induction (ηη_comp P z).
    apply idpath.
  Qed.

  Local Definition psnaturality_PPG_help
        (P : poly_code)
        {X Y : one_type}
        (f : X → Y)
        (z : PA₀ P X)
    : PA₁ P f (pr1 (poly_path_groupoid P X) z)
      =
      pr1 (poly_path_groupoid P Y) (PA₁ P f z)
    := pr11 (psnaturality_of (poly_path_groupoid P) f) z.

  Local Definition psnaturality_PGQ_help
        (P : poly_code)
        {G₁ G₂ : groupoid}
        (F : G₁ ⟶ G₂)
        (z : PA₀ P (gquot G₁))
    : GQ₁ (poly_act_functor P G₁ G₂ F) ((poly_gquot P) G₁ z)
      =
      (poly_gquot P) G₂ (PA₁ P (GQ₁ F) z)
    := pr1 (psnaturality_of (poly_gquot P) F) z.

  Definition maponpaths_homot
             {A B : UU}
             {f g : A → B}
             (e : f ~ g)
             {a₁ a₂ : A}
             (p : a₁ = a₂)
    : ap f p = e a₁ @ ap g p @ !(e a₂).
  Proof.
    induction p.
    exact (!(pathsinv0r _)).
  Qed.

  Local Definition lift_unit_help₄
        (P : poly_code)
        {x y : groupoid}
        (f : x ⟶ y)
        (z : poly_act P (pr1 x))           
    : ap (GQ₁ (poly_act_functor P x y f))
         (ηη_comp P z)
    @ psnaturality_PGQ_help
        P f ((pr1 ((poly_path_groupoid P) (GQ₀ x))) (PA₁ P (gcl x) z))
    @ ap ((poly_gquot P) y) (lift_unit_pstrans P x y f z)
    =
    ηη_comp P (PA₁ P f z).
  Proof.
    (*
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (@idpath _ (@idpath _ ((gcl (poly_act_groupoid (C A) y) z)))).
    - apply idpath.
    - induction z as [z | z].
      + refine (_ @ ap (ap gquot_inl_grpd) (IHP₁ z)).
        refine (!_).
        etrans.
        {
          refine (maponpathscomp0 _ _ _ @ _).
          apply maponpaths.
          apply maponpathscomp0.
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          refine (maponpathscomp inl (gquot_sum (poly_gquot P₁) (poly_gquot P₂) y) _ @ _).
          exact (!(maponpathscomp (poly_gquot P₁ y)
                               (@gquot_inl_grpd P₁ P₂ _)
                               (lift_unit_pstrans P₁ x y f z))).
        }
        refine (path_assoc _ _ _ @ _).
        refine (_ @ !(path_assoc _ _ _)). 
        apply maponpaths_2.
        refine (path_assoc
                  _
                  (gquot_inl_grpd_gquot_functor
                     f
                     (poly_gquot
                        P₁
                        x
                        (pr11 ((poly_path_groupoid P₁) (GQ₀ x))
                              (PA₁ P₁ (gcl x) z))))
                  (ap gquot_inl_grpd
                      (psnaturality_PGQ_help
                         P₁
                         f
                         _))
                  @ _).
        apply maponpaths_2.
        simpl.
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          exact (maponpathscomp
                   gquot_inl_grpd
                   (GQ₁ (poly_act_functor (P₁ + P₂) x y f))
                   (ηη_comp P₁ z)).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (maponpaths_homot (gquot_inl_grpd_gquot_functor f) (ηη_comp P₁ z)).
        }
        simpl.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(maponpathscomp
                     (λ z0, GQ₁ (poly_act_functor P₁ x y f) z0)
                     gquot_inl_grpd
                     (ηη_comp P₁ z))).
        }
        refine (_ @ pathscomp0rid _).
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        apply pathsinv0l.
      + refine (_ @ ap (ap gquot_inr_grpd) (IHP₂ z)).
        refine (!_).
        etrans.
        {
          refine (maponpathscomp0 _ _ _ @ _).
          apply maponpaths.
          apply maponpathscomp0.
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          refine (maponpathscomp inr (gquot_sum (poly_gquot P₁) (poly_gquot P₂) y) _ @ _).
          exact (!(maponpathscomp (poly_gquot P₂ y)
                                  (@gquot_inr_grpd P₁ P₂ _)
                                  (lift_unit_pstrans P₂ x y f z))).
        }
        refine (path_assoc _ _ _ @ _).
        refine (_ @ !(path_assoc _ _ _)). 
        apply maponpaths_2.
        refine (path_assoc
                  _
                  (gquot_inr_grpd_gquot_functor
                     f
                     (poly_gquot
                        P₂
                        x
                        (pr11 ((poly_path_groupoid P₂) (GQ₀ x))
                              (PA₁ P₂ (gcl x) z))))
                  (ap gquot_inr_grpd
                      (psnaturality_PGQ_help
                         P₂
                         f
                         _))
                  @ _).
        apply maponpaths_2.
        simpl.
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          exact (maponpathscomp
                   gquot_inr_grpd
                   (GQ₁ (poly_act_functor (P₁ + P₂) x y f))
                   (ηη_comp P₂ z)).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (maponpaths_homot (gquot_inr_grpd_gquot_functor f) (ηη_comp P₂ z)).
        }
        simpl.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(maponpathscomp
                     (λ z0, GQ₁ (poly_act_functor P₂ x y f) z0)
                     gquot_inr_grpd
                     (ηη_comp P₂ z))).
        }
        refine (_ @ pathscomp0rid _).
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        apply pathsinv0l.
    - refine (!_).
      etrans.
      {
        exact (ap (λ l, ap (λ z, gquot_prod_comp (pr1 z) (pr2 z))
                           (pathsdirprod
                              l
                              (ηη_comp P₂ (PA₁ P₂ f (pr2 z)))))
                  (!(IHP₁ (pr1 z)))).
      }
      etrans.
      {
        exact (ap (λ r, ap (λ z, gquot_prod_comp (pr1 z) (pr2 z))
                           (pathsdirprod
                              (ap (GQ₁ (poly_act_functor P₁ x y f)) (ηη_comp P₁ (pr1 z)) @
                                  psnaturality_PGQ_help P₁ f
                                  ((pr1 ((poly_path_groupoid P₁) (GQ₀ x))) (PA₁ P₁ (gcl x) (pr1 z))) @
                                  ap ((poly_gquot P₁) y) (lift_unit_pstrans P₁ x y f (pr1 z)))
                              r))
                  (!(IHP₂ (pr2 z)))).
      }*)
      apply TODO.
  Qed.
             
  Definition algebra_biadjunction_lift_unit_pstrans_nat_lem
             (P : poly_code)
             {x y : groupoid}
             {f : x ⟶ y}
             {xx : (⦃ P ⦄ x : groupoid) ⟶ x}
             {yy : (⦃ P ⦄ y : groupoid) ⟶ y}
             (ff : xx ∙ f ⟹ # ⦃ P ⦄ f ∙ yy)
             (z : poly_act P (pr1 x))
    : (gcleq y (pr1 ff z)
    @ ap (GQ₁ yy) (ηη_comp P (PA₁ P f z)))
    @ ap (λ x0, GQ₁ yy ((poly_gquot P) y x0))
         (# (pr1 ((poly_path_groupoid P) (GQ₀ y)))
            (PAC P x y (one_type_to_groupoid (GQ₀ y)) f (gquot_unit_functor y) z))
    =
    ((ap (GQ₁ f) (ap (GQ₁ xx) (ηη_comp P z))
    @ (((GQC xx f
             (poly_gquot P x (pr1 ((poly_path_groupoid P) (GQ₀ x))
                                  (PA₁ P (gcl x) z)))
    @ GQ₂ ff (poly_gquot P x
                         (pr1 ((poly_path_groupoid P) (GQ₀ x)) (PA₁ P (gcl x) z))))
    @ ! GQC (poly_act_functor P x y f) yy
            ((poly_gquot P) x (pr1 ((poly_path_groupoid P) (GQ₀ x)) (PA₁ P (gcl x) z))))
    @ ap (GQ₁ yy)
         (psnaturality_PGQ_help
            P f
            (pr1 ((poly_path_groupoid P) (GQ₀ x)) (PA₁ P (gcl x) z))))
    @ ap (λ x0, GQ₁ yy ((poly_gquot P) y x0))
         (psnaturality_PPG_help P (GQ₁ f) (PA₁ P (gcl x) z)))
    @ ap (λ x0, GQ₁ yy ((poly_gquot P) y x0))
         (# (pr1 ((poly_path_groupoid P) (GQ₀ y)))
            (PAC P x (one_type_to_groupoid (GQ₀ x)) (one_type_to_groupoid (GQ₀ y))
                 (gquot_unit_functor x) (function_to_functor (GQ₁ f)) z)))
    @ ap (λ x0, GQ₁ yy ((poly_gquot P) y x0))
         (# (pr1 ((poly_path_groupoid P) (GQ₀ y)))
            (PA₂ P x (one_type_to_groupoid (GQ₀ y))
                 (gquot_unit_functor x ∙ function_to_functor (GQ₁ f))
                 (f ∙ gquot_unit_functor y)
                 (gquot_unit_nat_trans x y f) z)).
  Proof.
    refine (!_).
    etrans.
    {
      do 2 refine (!(path_assoc _ _ _) @ _).  
      apply maponpaths.
      do 4 refine (!(path_assoc _ _ _) @ _).
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp0
                    (λ w : PA₀ P (gquot y), GQ₁ yy ((poly_gquot P) y w))
                    _ _)).
      }
      exact (!(maponpathscomp0
                    (λ w : PA₀ P (gquot y), GQ₁ yy ((poly_gquot P) y w))
                    _ _)).
    }
    etrans.
    {
      do 5 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (lift_unit_pstrans_eq f z).
      }
      exact ((maponpathscomp0
                 (λ w : PA₀ P (gquot y), GQ₁ yy ((poly_gquot P) y w))
                 _ _)).
    }
    do 5 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    do 4 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp ((poly_gquot P) y) (GQ₁ yy) _)).
      }
      exact (!(maponpathscomp0 (GQ₁ yy) _ _)).
    }
    do 3 refine (path_assoc _ _ _ @ _).
    etrans.
    {
      do 3 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp (GQ₁ xx) (GQ₁ f) (ηη_comp P z)).
      }
      exact (lift_unit_help₁ P f xx z).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (lift_unit_help₂ P ff z).
    }
    do 2 refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (lift_unit_help₃ P ff z).
    }
    etrans.
    {
      exact (!(maponpathscomp0
                 (GQ₁ yy)
                 (ap (GQ₁ (poly_act_functor P x y f)) (ηη_comp P z))
                 _)).
    }
    apply maponpaths.
    exact (lift_unit_help₄ P f z).
  Qed.

  Definition algebra_biadjunction_lift_unit_pstrans_nat
             (P : poly_code)
    : algebra_lift_pstrans_nat
        (unit_of_lifted_biadj
           gquot_biadj_data (poly_gquot P) (poly_path_groupoid P)
           (ηη P)).
  Proof.
    intros x y f xx yy ff.
    use nat_trans_eq.
    { apply homset_property. }
    intro z.
    (*Transparent ps_comp.
    simpl.
    cbn.
    unfold homotcomp, funhomotsec, invhomot, homotfun.
    cbn.
    rewrite !pathscomp0rid.
    exact (algebra_biadjunction_lift_unit_pstrans_nat_lem P (pr1 ff) z).*)
    apply TODO.
  Qed.
End LiftUnitHelp.
