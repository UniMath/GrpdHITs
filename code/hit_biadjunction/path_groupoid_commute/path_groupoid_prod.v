(** Commutation of path groupoid with products *)
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

(** Commutation with product *)
Section PathGroupoidProd.
  Context {P₁ P₂ : poly_code}
          (IHP₁ : pstrans
                    (ps_comp ⦃ P₁ ⦄ path_groupoid)
                    (ps_comp path_groupoid (⟦ P₁ ⟧)))
          (IHP₂ : pstrans
                    (ps_comp ⦃ P₂ ⦄ path_groupoid)
                    (ps_comp path_groupoid (⟦ P₂ ⟧))).
  
  Definition path_groupoid_prod_data_comp_data
             (X : one_types)
    : functor_data
        ((ps_comp ⦃ P₁ * P₂ ⦄ path_groupoid) X : groupoid)
        ((ps_comp path_groupoid (⟦ P₁ * P₂ ⟧)) X : groupoid).
  Proof.
    use make_functor_data.
    - intros z.
      exact (pr1 (IHP₁ X) (pr1 z) ,, pr1 (IHP₂ X) (pr2 z)).
    - intros z₁ z₂ f.
      apply pathsdirprod.
      + exact (#(pr1 (IHP₁ X)) (pr1 f)).
      + exact (#(pr1 (IHP₂ X)) (pr2 f)).
  Defined.

  Definition path_groupoid_prod_data_laws
             (X : one_types)
    : is_functor (path_groupoid_prod_data_comp_data X).
  Proof.
    split.
    - intros z.
      refine (maponpaths (pathsdirprod _) (functor_id (IHP₂ X) _) @ _).
      exact (maponpaths (λ z, pathsdirprod z _) (functor_id (IHP₁ X) _)).
    - intros z₁ z₂ z₃ f g.
      refine (maponpaths (pathsdirprod _) (functor_comp (IHP₂ X) _ _) @ _).
      refine (maponpaths (λ z, pathsdirprod z _) (functor_comp (IHP₁ X) _ _) @ _).
      refine (!_).
      apply pathsdirprod_concat.
  Qed.

  Definition path_groupoid_prod_data_comp
             (X : one_types)
    : functor
        ((ps_comp ⦃ P₁ * P₂ ⦄ path_groupoid) X : groupoid)
        ((ps_comp path_groupoid (⟦ P₁ * P₂ ⟧)) X : groupoid).
  Proof.
    use make_functor.
    - exact (path_groupoid_prod_data_comp_data X).
    - exact (path_groupoid_prod_data_laws X).
  Defined.

  Definition path_groupoid_prod_data_nat_data
             {X Y : one_types}
             (f : X --> Y)
    : nat_trans_data
        (path_groupoid_prod_data_comp X ∙ # (ps_comp path_groupoid (⟦ P₁ * P₂ ⟧)) f)
        (# (ps_comp ⦃ P₁ * P₂ ⦄ path_groupoid) f ∙ path_groupoid_prod_data_comp Y).
  Proof.
    intros z.
    apply pathsdirprod.
    - exact (pr11 (psnaturality_of IHP₁ f) (pr1 z)).
    - exact (pr11 (psnaturality_of IHP₂ f) (pr2 z)).
  Defined.

  Definition path_groupoid_prod_data_nat_is_nat_trans
             {X Y : one_types}
             (f : X --> Y)
    : is_nat_trans _ _ (path_groupoid_prod_data_nat_data f).
  Proof.
    intros z₁ z₂ g.
    refine (_ @ !(pathsdirprod_concat _ _ _ _)).
    refine (maponpaths (λ z, z @ _) (!(maponpaths_pathsdirprod _ _ _ _)) @ _).
    refine (pathsdirprod_concat _ _ _ _ @ _).
    refine (maponpaths
              (λ z, pathsdirprod z _)
              (pr21 (psnaturality_of IHP₁ f) _ _ (pr1 g))
              @ _).
    exact (maponpaths
             (pathsdirprod _)
             (pr21 (psnaturality_of IHP₂ f) _ _ (pr2 g))).
  Qed.
  
  Definition path_groupoid_prod_data_nat
             {X Y : one_types}
             (f : X --> Y)
    : (path_groupoid_prod_data_comp X)
        ∙ # (ps_comp path_groupoid (⟦ P₁ * P₂ ⟧)) f
        ⟹
        # (ps_comp ⦃ P₁ * P₂ ⦄ path_groupoid) f ∙ path_groupoid_prod_data_comp Y.
  Proof.
    use make_nat_trans.
    - exact (path_groupoid_prod_data_nat_data f).
    - exact (path_groupoid_prod_data_nat_is_nat_trans f).
  Defined.
        
  Definition path_groupoid_prod_data
    : pstrans_data
        (ps_comp ⦃ P₁ * P₂ ⦄ path_groupoid)
        (ps_comp path_groupoid (⟦ P₁ * P₂ ⟧)).
  Proof.
    use make_pstrans_data.
    - exact path_groupoid_prod_data_comp.
    - intros X Y f.
      use tpair.
      + exact (path_groupoid_prod_data_nat f).
      + apply grpd_bicat_is_invertible_2cell.
  Defined.

  Definition path_groupoid_prod_is_pstrans
    : is_pstrans path_groupoid_prod_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use nat_trans_eq.
      { apply homset_property. }
      intro z.
      refine (pathsdirprod_concat _ _ _ _ @ _).
      refine (_ @ !(pathsdirprod_concat _ _ _ _)).
      refine (maponpaths
                (λ z, pathsdirprod z _)
                (nat_trans_eq_pointwise (psnaturality_natural IHP₁ X Y f g p) (pr1 z))
                @ _).
      exact (maponpaths
               (pathsdirprod _)
               (nat_trans_eq_pointwise (psnaturality_natural IHP₂ X Y f g p) (pr2 z))).
    - intros X.
      use nat_trans_eq.
      { apply homset_property. }
      intro z.
      refine (pathsdirprod_concat _ _ _ _ @ _).
      refine (maponpaths
                (λ z, pathsdirprod z _)
                (nat_trans_eq_pointwise (pstrans_id IHP₁ X) (pr1 z))
                @ _).
      exact (maponpaths
               (pathsdirprod _)
               (nat_trans_eq_pointwise (pstrans_id IHP₂ X) (pr2 z))).
    - intros X Y Z f g.
      use nat_trans_eq.
      { apply homset_property. }
      intro z.
      refine (pathsdirprod_concat _ _ _ _ @ _).
      refine (maponpaths
                (λ z, pathsdirprod z _)
                (nat_trans_eq_pointwise (pstrans_comp IHP₁ f g) (pr1 z))
                @ _).
      refine (maponpaths
                (pathsdirprod _)
                (nat_trans_eq_pointwise (pstrans_comp IHP₂ f g) (pr2 z))
                @ _).
      refine (!_).
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        etrans.
        {
          apply pathscomp0rid.
        }
        exact (!(path_assoc _ _ _)).
      }
      refine (!(path_assoc _ _ _) @ _).
      refine (maponpaths (λ z, _ @ z) _ @ _).
      {
        apply pathsdirprod_concat.
      }
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        refine (!_).
        apply (maponpaths_pathsdirprod (# (⟦ P₁ ⟧) g) (# (⟦ P₂ ⟧) g)).
      }
      etrans.
      {
        apply pathsdirprod_concat.
      }
      refine (!_).
      etrans.
      {
        refine (maponpaths
                  (λ z, pathsdirprod (z @ _) _)
                  _).
        etrans.
        {
          apply pathscomp0rid.
        }
        exact (maponpaths (λ z, z @ pr11 (psnaturality_of IHP₁ g) _) (pathscomp0rid _)).
      }
      etrans.
      {
        refine (maponpaths
                  (λ z, pathsdirprod _ (z @ _))
                  (pathscomp0rid _ @ _)
               ).
        exact (maponpaths (λ z, z @ pr11 (psnaturality_of IHP₂ g) _) (pathscomp0rid _)).
      }
      refine (maponpaths
                (λ z, pathsdirprod z _)
                (!(path_assoc _ _ _)) @ _).
      exact (maponpaths
               (λ z, pathsdirprod _ z)
               (!(path_assoc _ _ _))).
  Qed.      
  
  Definition path_groupoid_prod
    : pstrans
        (ps_comp ⦃ P₁ * P₂ ⦄ path_groupoid)
        (ps_comp path_groupoid (⟦ P₁ * P₂ ⟧)).
  Proof.
    use make_pstrans.
    - exact path_groupoid_prod_data.
    - exact path_groupoid_prod_is_pstrans.
  Defined.
End PathGroupoidProd.
