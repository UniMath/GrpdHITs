Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
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

Require Import prelude.cubical_methods.
Require Import prelude.grpd_bicat.
Require Import groupoid_quotient.gquot.
Require Import groupoid_quotient.gquot_principles.
Require Import gquot_biadjunction.gquot_functor.
Require Import gquot_biadjunction.path_groupoid.

Local Open Scope cat.

Section GQuotUnit.
  Variable (G : groupoid).

  Definition gquot_unit_functor_data
    : functor_data G (one_type_to_groupoid_precategory_data (gquot_functor_obj G)).
  Proof.
    use make_functor_data.
    - exact (gcl G).
    - exact (@gcleq G).
  Defined.

  Definition gquot_unit_functor_is_functor
    : is_functor gquot_unit_functor_data.
  Proof.
    split.
    - intros x ; cbn.
      apply ge.
    - intros x y z f g ; cbn.
      apply gconcat.
  Qed.
  
  Definition gquot_unit_functor
    : G ⟶ one_type_to_groupoid_precategory_data (gquot_functor_obj G).
  Proof.
    use make_functor.
    - exact gquot_unit_functor_data.
    - exact gquot_unit_functor_is_functor.
  Defined.
End GQuotUnit.

Definition gquot_unit_nat_trans_data
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : nat_trans_data
      (gquot_unit_functor G₁ ∙ function_to_functor (gquot_functor_map F))
      (F ∙ gquot_unit_functor G₂)
  := λ _, idpath _.

Definition gquot_unit_nat_trans_is_nat_trans
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : is_nat_trans _ _ (gquot_unit_nat_trans_data G₁ G₂ F).
Proof.
  intros x y f ; cbn.
  unfold gquot_unit_nat_trans_data ; cbn.
  refine (pathscomp0rid _ @ _).
  exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
Qed.

Definition gquot_unit_nat_trans
           (G₁ G₂ : groupoid)
           (F : G₁ ⟶ G₂)
  : (gquot_unit_functor G₁ ∙ function_to_functor (gquot_functor_map F))
      ⟹
      F ∙ gquot_unit_functor G₂.
Proof.
  use make_nat_trans.
  - exact (gquot_unit_nat_trans_data G₁ G₂ F).
  - exact (gquot_unit_nat_trans_is_nat_trans G₁ G₂ F).
Defined.

Definition gquot_unit_data
  : pstrans_data
      (id_psfunctor grpd_bicat)
      (comp_psfunctor path_groupoid gquot_psfunctor).
Proof.
  use make_pstrans_data.
  - exact gquot_unit_functor.
  - intros G₁ G₂ F ; cbn.
    use make_invertible_2cell.
    + exact (gquot_unit_nat_trans G₁ G₂ F).
    + apply grpd_bicat_is_invertible_2cell.
Defined.

Definition gquot_unit_is_pstrans
  : is_pstrans gquot_unit_data.
Proof.
  repeat split.
  - intros G₁ G₂ F₁ F₂ α.
    use nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    unfold gquot_unit_nat_trans_data ; cbn.
    apply pathscomp0rid.
  - intros G.
    use nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    unfold gquot_unit_nat_trans_data ; cbn.
    exact (!(ge G x)).
  - intros G₁ G₂ G₃ F₁ F₂.
    use nat_trans_eq.
    { apply homset_property. }
    intros x ; cbn.
    unfold gquot_unit_nat_trans_data ; cbn.
    exact (!(ge G₃ _)).
Qed.

Definition gquot_unit
  : pstrans
      (id_psfunctor grpd_bicat)
      (comp_psfunctor path_groupoid gquot_psfunctor).
Proof.
  use make_pstrans.
  - exact gquot_unit_data.
  - exact gquot_unit_is_pstrans.
Defined.

Definition gquot_counit_map
           (X : one_type)
  : one_types ⟦ gquot_functor_obj (one_type_to_groupoid X) , X ⟧.
Proof.
  use gquot_rec.
  - exact (λ x, x).
  - exact (λ _ _ p, p).
  - exact (λ _, idpath _).
  - exact (λ _ _ _ _ _, idpath _).
  - apply X.
Defined.

Definition gquot_counit_data_po
           (X Y : one_types)
           (f : X --> Y)
           (x₁ x₂ : (X : one_type))
           (p : x₁ = x₂)
  : @PathOver
      _
      (gcl (path_groupoid X) x₁) (gcl (path_groupoid X) x₂)
      (λ z : gquot (path_groupoid X),
             (gquot_counit_map X · # (id_psfunctor one_types) f) z
             =
             (# (comp_psfunctor gquot_psfunctor path_groupoid) f · gquot_counit_map Y) z)
      (idpath _)
      (idpath _)
      (gcleq (one_type_to_groupoid X) p).
Proof.
  use map_PathOver.
  unfold square ; cbn.
  rewrite pathscomp0rid.
  induction p.
  rewrite ge.
  cbn.
  apply idpath.
Qed.

Definition gquot_counit_naturality
           {X Y : one_type}
           (f : X → Y)
  : (f ∘ gquot_counit_map X)%functions
    ~
    (gquot_counit_map Y ∘ gquot_functor_map (function_to_functor f))%functions.
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - exact (gquot_counit_data_po X Y f).
  - intros x.
    exact (one_type_isofhlevel Y _ _).
Defined.

Definition gquot_counit_data
  : pstrans_data
      (comp_psfunctor gquot_psfunctor path_groupoid)
      (id_psfunctor one_types).
Proof.
  use make_pstrans_data.
  - exact gquot_counit_map.
  - intros X Y f.
    use make_invertible_2cell.
    + exact (gquot_counit_naturality f).
    + apply one_type_2cell_iso.
Defined.

Definition gquot_counit_is_pstrans
  : is_pstrans gquot_counit_data.
Proof.
  repeat split.
  - intros X Y f g p ; cbn.
    use funextsec.
    unfold homotsec.
    use gquot_ind_prop.
    + intro x ; cbn.
      unfold homotcomp, funhomotsec, homotfun, gquot_counit_map ; cbn.
      rewrite pathscomp0rid.
      rewrite gquot_rec_beta_gcleq.
      apply idpath.
    + intro.
      exact (one_type_isofhlevel Y _ _ _ _).
  - intros X.
    use funextsec.
    unfold homotsec.
    use gquot_ind_prop.
    + intro x ; cbn.
      unfold homotcomp, funhomotsec, homotfun, gquot_counit_map ; cbn.
      rewrite gquot_rec_beta_gcleq.
      apply idpath.
    + intro.
      exact (one_type_isofhlevel X _ _ _ _).
  - intros X Y Z f g.
    use funextsec.
    unfold homotsec.
    use gquot_ind_prop.
    + intro x ; cbn.
      unfold homotcomp, funhomotsec, homotfun, gquot_counit_map ; cbn.
      rewrite gquot_rec_beta_gcleq.
      apply idpath.
    + intro.
      exact (one_type_isofhlevel Z _ _ _ _).
Qed.      
      
Definition gquot_counit
  : pstrans
      (comp_psfunctor gquot_psfunctor path_groupoid)
      (id_psfunctor one_types).
Proof.
  use make_pstrans.
  - exact gquot_counit_data.
  - exact gquot_counit_is_pstrans.
Defined.

Definition gquot_biadj_unit_counit
  : left_biadj_unit_counit gquot_psfunctor.
Proof.
  use make_biadj_unit_counit.
  - exact path_groupoid.
  - exact gquot_unit.
  - exact gquot_counit.
Defined.

Definition gquot_biadj_triangle_l_data_po
           (G : groupoid)
           (x₁ x₂ : G)
           (f : x₁ --> x₂)
  : @PathOver
      _
      (gcl G x₁) (gcl G x₂)
      (λ z,
       biadj_triangle_l_lhs gquot_biadj_unit_counit G z
       =
       id_pstrans gquot_psfunctor G z)
      (idpath ((biadj_triangle_l_lhs gquot_biadj_unit_counit) G (gcl G x₁)))
      (idpath ((biadj_triangle_l_lhs gquot_biadj_unit_counit) G (gcl G x₂)))
      (gcleq G f).
Proof.
  apply map_PathOver.
  unfold square.
  refine (pathscomp0rid _ @ _).
  refine (_ @ !(maponpathsidfun _)).
  cbn.
  refine (!(maponpathscomp (gquot_functor_map _) _ (gcleq G f)) @ _).
  etrans.
  {
    apply maponpaths.
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  }
  exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
Qed.

Definition gquot_biadj_triangle_l_data_cell
           (G : groupoid)
  : biadj_triangle_l_lhs gquot_biadj_unit_counit G ==> id_pstrans gquot_psfunctor G.
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - exact (gquot_biadj_triangle_l_data_po G).
  - intro.
    exact (gtrunc G _ _).
Defined.

Definition gquot_biadj_triangle_l_data
  : invertible_modification_data
      (biadj_triangle_l_lhs gquot_biadj_unit_counit)
      (id_pstrans gquot_psfunctor).
Proof.
  intros G.
  use make_invertible_2cell.
  - exact (gquot_biadj_triangle_l_data_cell G).
  - apply one_type_2cell_iso.
Defined.

Definition gquot_biadj_triangle_l_is_modification
  : is_modification gquot_biadj_triangle_l_data.
Proof.
  intros G₁ G₂ F.
  use funextsec.
  use gquot_ind_prop.
  - intro a.
    cbn.
    unfold homotcomp, funhomotsec, homotfun, gquot_counit_map ; cbn.
    rewrite !pathscomp0rid.
    unfold gquot_unit_nat_trans_data ; cbn.
    rewrite gquot_rec_beta_gcleq.
    apply idpath.
  - intro.
    exact (gtrunc G₂ _ _ _ _).
Qed.  

Definition gquot_biadj_triangle_l
  : biadj_triangle_l_law gquot_biadj_unit_counit.
Proof.
  use make_invertible_modification.
  - exact gquot_biadj_triangle_l_data.
  - exact gquot_biadj_triangle_l_is_modification.
Defined.

Definition gquot_biadj_triangle_r_data
  : invertible_modification_data
      (biadj_triangle_r_lhs gquot_biadj_unit_counit)
      (id_pstrans gquot_biadj_unit_counit).
Proof.
  intros X.
  use make_invertible_2cell.
  - use make_nat_trans.
    + exact idpath.
    + abstract
        (intros x y p ;
         cbn in * ;
         rewrite pathscomp0rid ;
         exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)).
  - apply grpd_bicat_is_invertible_2cell.
Defined.

Definition gquot_biadj_triangle_r_is_modification
  : is_modification gquot_biadj_triangle_r_data.
Proof.
  intros X Y f.
  use nat_trans_eq.
  { apply homset_property. }
  intros x ; cbn.
  rewrite !pathscomp0rid.
  exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
Qed.

Definition gquot_biadj_triangle_r
  : biadj_triangle_r_law gquot_biadj_unit_counit.
Proof.
  use make_invertible_modification.
  - exact gquot_biadj_triangle_r_data.
  - exact gquot_biadj_triangle_r_is_modification.
Defined.

Definition gquot_biadj_data
  : left_biadj_data gquot_psfunctor.
Proof.
  use make_biadj_data.
  - exact gquot_biadj_unit_counit.
  - exact gquot_biadj_triangle_l.
  - exact gquot_biadj_triangle_r.
Defined.
