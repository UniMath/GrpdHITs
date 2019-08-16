(** Commutation of path groupoid with sums *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

Opaque ps_comp.

(** Commutation with sums *)
Section PathGroupoidSum.
  Context {P₁ P₂ : poly_code}
          (IHP₁ : pstrans
                    (ps_comp ⦃ P₁ ⦄ path_groupoid)
                    (ps_comp path_groupoid (⟦ P₁ ⟧)))
          (IHP₂ : pstrans
                    (ps_comp ⦃ P₂ ⦄ path_groupoid)
                    (ps_comp path_groupoid (⟦ P₂ ⟧))).

  Definition path_groupoid_sum_data_comp_data
             (X : one_types)
    : functor_data
        ((ps_comp ⦃ P₁ + P₂ ⦄ path_groupoid) X : groupoid)
        ((ps_comp path_groupoid (⟦ P₁ + P₂ ⟧)) X : groupoid).
  Proof.
    use make_functor_data.
    - intros z.
      induction z as [z | z].
      + exact (inl (pr1 (IHP₁ X) z)).
      + exact (inr (pr1 (IHP₂ X) z)).
    - intros z₁ z₂ f.
      induction z₁ as [z₁ | z₁], z₂ as [z₂ | z₂].
      + exact (maponpaths inl (#(pr1 (IHP₁ X)) f)).
      + exact (fromempty f).
      + exact (fromempty f).
      + exact (maponpaths inr (#(pr1 (IHP₂ X)) f)).
  Defined.

  Definition path_groupoid_sum_data_laws
             (X : one_types)
    : is_functor (path_groupoid_sum_data_comp_data X).
  Proof.
    split.
    - intros z.
      induction z as [z | z].
      + exact (maponpaths (maponpaths inl) (functor_id (IHP₁ X) _)).
      + exact (maponpaths (maponpaths inr) (functor_id (IHP₂ X) _)).
    - intros z₁ z₂ z₃ f g.
      induction z₁ as [z₁ | z₁], z₂ as [z₂ | z₂], z₃ as [z₃ | z₃].
      + refine (maponpaths (maponpaths inl) (functor_comp (IHP₁ X) f g) @ _).
        apply (maponpathscomp0 inl).
      + exact (fromempty g).
      + exact (fromempty f).
      + exact (fromempty f).
      + exact (fromempty f).
      + exact (fromempty f).
      + exact (fromempty g).
      + refine (maponpaths (maponpaths inr) (functor_comp (IHP₂ X) f g) @ _).
        apply (maponpathscomp0 inr).
  Qed.

  Definition path_groupoid_sum_data_comp
             (X : one_types)
    : functor
        ((ps_comp ⦃ P₁ + P₂ ⦄ path_groupoid) X : groupoid)
        ((ps_comp path_groupoid (⟦ P₁ + P₂ ⟧)) X : groupoid).
  Proof.
    use make_functor.
    - exact (path_groupoid_sum_data_comp_data X).
    - exact (path_groupoid_sum_data_laws X).
  Defined.

  Definition path_groupoid_sum_data_nat_data
             {X Y : one_types}
             (f : X --> Y)
    : nat_trans_data
        (path_groupoid_sum_data_comp X ∙ # (ps_comp path_groupoid (⟦ P₁ + P₂ ⟧)) f)
        (# (ps_comp ⦃ P₁ + P₂ ⦄ path_groupoid) f ∙ path_groupoid_sum_data_comp Y).
  Proof.
    intros z.
    induction z as [z | z].
    - exact (maponpaths inl (pr11 (psnaturality_of IHP₁ f) z)).
    - exact (maponpaths inr (pr11 (psnaturality_of IHP₂ f) z)).
  Defined.

  Definition path_groupoid_sum_data_nat_is_nat_trans
             {X Y : one_types}
             (f : X --> Y)
    : is_nat_trans _ _ (path_groupoid_sum_data_nat_data f).
  Proof.
    intros z₁ z₂ g.
    induction z₁ as [z₁ | z₁], z₂ as [z₂ | z₂].
    - refine (_ @ maponpaths (maponpaths inl) (pr21 (psnaturality_of IHP₁ f) _ _ g)
                @ maponpathscomp0 inl _ _).
      refine (_ @ !(maponpathscomp0 inl _ _)).
      apply maponpaths_2.
      refine (maponpathscomp inl (coprodf (#(⟦ P₁ ⟧) f) (#(⟦ P₂ ⟧) f)) _ @ _).
      exact (!(maponpathscomp (#(⟦ P₁ ⟧) f) inl _)).
    - exact (fromempty g).
    - exact (fromempty g).
    - refine (_ @ maponpaths (maponpaths inr) (pr21 (psnaturality_of IHP₂ f) _ _ g)
                @ maponpathscomp0 inr _ _).
      refine (_ @ !(maponpathscomp0 inr _ _)).
      apply maponpaths_2.
      refine (maponpathscomp inr (coprodf (#(⟦ P₁ ⟧) f) (#(⟦ P₂ ⟧) f)) _ @ _).
      exact (!(maponpathscomp (#(⟦ P₂ ⟧) f) inr _)).
  Qed.
      
  Definition path_groupoid_sum_data_nat
             {X Y : one_types}
             (f : X --> Y)
    : (path_groupoid_sum_data_comp X)
        ∙ # (ps_comp path_groupoid (⟦ P₁ + P₂ ⟧)) f
        ⟹
        # (ps_comp ⦃ P₁ + P₂ ⦄ path_groupoid) f ∙ path_groupoid_sum_data_comp Y.
  Proof.
    use make_nat_trans.
    - exact (path_groupoid_sum_data_nat_data f).
    - exact (path_groupoid_sum_data_nat_is_nat_trans f).
  Defined.
        
  Definition path_groupoid_sum_data
    : pstrans_data
        (ps_comp ⦃ P₁ + P₂ ⦄ path_groupoid)
        (ps_comp path_groupoid (⟦ P₁ + P₂ ⟧)).
  Proof.
    use make_pstrans_data.
    - exact path_groupoid_sum_data_comp.
    - intros X Y f.
      use tpair.
      + exact (path_groupoid_sum_data_nat f).
      + apply grpd_bicat_is_invertible_2cell.
  Defined.

  Definition path_groupoid_sum_is_pstrans
    : is_pstrans path_groupoid_sum_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use nat_trans_eq.
      { apply homset_property. }
      intro z.
      induction z as [z | z].
      + refine (!(maponpathscomp0 inl _ _) @ _ @ maponpathscomp0 inl _ _).
        refine (maponpaths (maponpaths inl) _).
        exact (nat_trans_eq_pointwise (psnaturality_natural IHP₁ X Y f g p) z).
      + refine (!(maponpathscomp0 inr _ _) @ _ @ maponpathscomp0 inr _ _).
        refine (maponpaths (maponpaths inr) _).
        exact (nat_trans_eq_pointwise (psnaturality_natural IHP₂ X Y f g p) z).
    - intros X.
      use nat_trans_eq.
      { apply homset_property. }
      intro z.
      induction z as [z | z].
      + refine (!(maponpathscomp0 inl _ _) @ _).
        refine (maponpaths (maponpaths inl) _).
        refine (nat_trans_eq_pointwise (pstrans_id IHP₁ X) z @ _).
        apply idpath.
      + refine (!(maponpathscomp0 inr _ _) @ _).
        refine (maponpaths (maponpaths inr) _).
        refine (nat_trans_eq_pointwise (pstrans_id IHP₂ X) z @ _).
        apply idpath.
    - intros X Y Z f g.
      use nat_trans_eq.
      { apply homset_property. }
      intros z.
      induction z as [z | z].
      + refine (!(maponpathscomp0 inl _ _) @ _).
        refine (!_).
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          etrans.
          {
            apply pathscomp0rid.
          }
          refine (maponpaths (λ z, z @ _) _).
          apply pathscomp0rid.
        }
        etrans.
        {
          refine (maponpaths (λ z, (z @ _) @ _) _).
          refine (maponpathscomp inl (coprodf (#(⟦ P₁ ⟧) g) (#(⟦ P₂ ⟧) g)) _ @ _).
          exact (!(maponpathscomp (#(⟦ P₁ ⟧) g) inl _)).
        }
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          exact (!(maponpathscomp0 inl _ _)).
        }
        refine (!(maponpathscomp0 inl _ _) @ _).
        apply (maponpaths (maponpaths inl)).
        refine (_ @ !(nat_trans_eq_pointwise (pstrans_comp IHP₁ f g) z)).
        refine (!_).
        refine (maponpaths (λ z, z @ _) _).
        etrans.
        {
          apply pathscomp0rid.
        }
        refine (maponpaths (λ z, z @ _) _).
        apply pathscomp0rid.
      + refine (!(maponpathscomp0 inr _ _) @ _).
        refine (!_).
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          etrans.
          {
            apply pathscomp0rid.
          }
          refine (maponpaths (λ z, z @ _) _).
          apply pathscomp0rid.
        }
        etrans.
        {
          refine (maponpaths (λ z, (z @ _) @ _) _).
          refine (maponpathscomp inr (coprodf (#(⟦ P₁ ⟧) g) (#(⟦ P₂ ⟧) g)) _ @ _).
          exact (!(maponpathscomp (#(⟦ P₂ ⟧) g) inr _)).
        }
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          exact (!(maponpathscomp0 inr _ _)).
        }
        refine (!(maponpathscomp0 inr _ _) @ _).
        apply (maponpaths (maponpaths inr)).
        refine (_ @ !(nat_trans_eq_pointwise (pstrans_comp IHP₂ f g) z)).
        refine (!_).
        refine (maponpaths (λ z, z @ _) _).
        etrans.
        {
          apply pathscomp0rid.
        }
        refine (maponpaths (λ z, z @ _) _).
        apply pathscomp0rid.
  Qed.

  Definition path_groupoid_sum
    : pstrans
        (ps_comp ⦃ P₁ + P₂ ⦄ path_groupoid)
        (ps_comp path_groupoid (⟦ P₁ + P₂ ⟧)).
  Proof.
    use make_pstrans.
    - exact path_groupoid_sum_data.
    - exact path_groupoid_sum_is_pstrans.
  Defined.
End PathGroupoidSum.
