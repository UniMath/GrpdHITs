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
Require Export hit_biadjunction.hit_prealgebra_biadj.lift_path_groupoid.
Require Export hit_biadjunction.hit_prealgebra_biadj.lift_gquot.

Local Open Scope cat.

Local Definition TODO {A : UU} : A.
Admitted.

Definition koe
           (P : poly_code)
           {X : one_types}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : poly_gquot P (one_type_to_groupoid X) z
    =
    gcl (⦃ P ⦄ (one_type_to_groupoid X))
        (poly_map P (gquot_counit_map X) z).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + intros a₁ a₂ g.
      induction g.
      apply map_PathOver.
      apply TODO.
    + exact (λ _, gtrunc _ _ _).
  - induction z as [z | z].
    + exact (maponpaths gquot_inl_grpd (IHP₁ z)).
    + exact (maponpaths gquot_inr_grpd (IHP₂ z)).
  - exact (maponpaths
             (λ z, prod_gquot_comp (pr1 z) (dirprod_pr2 z))
             (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z)))).
Defined.

Definition koe2
           (P : poly_code)
           {X : one_types}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : pr1 (pr111 (poly_path_groupoid P) X) (poly_map P (gquot_counit_map X) z)
    =
    poly_map P (gquot_counit_map X) z.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + intros a₁ a₂ g.
      induction g.
      apply map_PathOver.
      apply TODO.
    + exact (λ _, one_type_isofhlevel _ _ _).
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
Defined.

Section LiftCounit.
  Variable (P : poly_code).

  Definition prealg_counit_comp
             {X : one_types}
             (hX : (disp_alg_bicat (⟦ P ⟧)) X)
             (z : poly_act P (gquot (one_type_to_groupoid X)))
    : gquot_counit_map
        X
        (gquot_functor_map
           (prealg_path_groupoid_map P X hX)
           (poly_gquot
              P
              (one_type_to_groupoid X)
              z))
      =
      hX (poly_map P (gquot_counit_map X) z)
    := maponpaths
         (λ z, gquot_counit_map
                 X
                 ((gquot_functor_map (prealg_path_groupoid_map P X hX) z)))
         (koe P z)
     @ maponpaths
         hX
         (koe2 P z).
  
  Definition prealg_counit
    : disp_pstrans
        (disp_pseudo_comp
           gquot_biadj_data
           gquot_psfunctor
           _
           _
           _
           (prealg_path_groupoid P)
           (prealg_gquot P))
        (disp_pseudo_id (disp_alg_bicat (⟦ P ⟧)))
        (biadj_counit gquot_biadj_data).
  Proof.
    use make_disp_pstrans.
    - apply disp_2cells_isaprop_alg.
    - apply disp_locally_groupoid_alg.
    - intros X hX.
      use make_invertible_2cell.
      + exact (prealg_counit_comp hX).
      + apply one_type_2cell_iso.
    - intros X Y f hX hY hf.
      use funextsec.
      intro z.
      Locate TODO.
      apply TODO.
      (*simpl in z.
      simpl.
      cbn.
      unfold homotcomp, funhomotsec, homotfun.
      cbn.
      rewrite !pathscomp0rid.
       *)
  Defined.
End LiftCounit.
