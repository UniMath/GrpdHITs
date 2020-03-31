Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import prelude.all.

Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.

Local Open Scope cat.

Local Arguments ii1_injectivity {_ _ _ _} _.
Local Arguments ii2_injectivity {_ _ _ _} _.

(**
Some operations needed for displayed algebras
 *)
Definition poly_dact_const
           (P : poly_code)
           {X Y : one_type}
           (x : poly_act P X)
  : poly_dact P (λ (z : X), Y) x → poly_act P Y.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idfun _).
  - exact (idfun _).
  - induction x as [x | x].
    + exact (λ z, inl (IHP₁ x z)).
    + exact (λ z, inr (IHP₂ x z)).
  - exact (λ z, IHP₁ (pr1 x) (pr1 z) ,, IHP₂ (pr2 x) (pr2 z)).
Defined.

Definition poly_dmap_const
           (P : poly_code)
           {X Y : one_type}
           (x : poly_act P X)
           (f : X → Y)
  : poly_dact_const P x (poly_dmap P (λ (z : X), Y) f x)
    =
    poly_map P f x.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + simpl ; cbn.
      apply maponpaths.
      exact (IHP₁ x).
    + simpl ; cbn.
      apply maponpaths.
      exact (IHP₂ x).
  - apply pathsdirprod.
    + exact (IHP₁ (pr1 x)).
    + exact (IHP₂ (pr2 x)).
Defined.

Definition endpoint_dact_const
           {A : poly_code}
           {P Q : poly_code}
           (X Y : total_bicat (disp_alg_bicat (⟦ A ⟧)))
           (e : endpoint A P Q)
           {z : poly_act P (pr1 X : one_type)}
           (y : poly_dact P (λ _, pr1 Y) z)
  : poly_dact_const
      Q
      (sem_endpoint_one_types e X z)
      (endpoint_dact
         X _ e
         (λ x y, pr2 Y (poly_dact_const A x y))
         y)
    =
    sem_endpoint_one_types e Y (poly_dact_const P z y).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ]
  ; try apply idpath.
  - simpl.
    exact (IHe₂ _ _ @ maponpaths _ (IHe₁ _ _)).
  - exact (pathsdirprod (IHe₁ _ _) (IHe₂ _ _)).
Defined.

Definition PathOver_poly_dact_const_eq
           {P : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P X}
           (y₁ : poly_dact_UU P (λ _ : X, Y) x₁)
           (y₂ : poly_dact_UU P (λ _ : X, Y) x₂)
  : UU
  := poly_dact_const P x₁ y₁ = poly_dact_const P x₂ y₂.

Definition PathOver_poly_dact_const
           {P : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P X}
           (p : x₁ = x₂)
           {y₁ : poly_dact_UU P (λ _ : X, Y) x₁}
           {y₂ : poly_dact_UU P (λ _ : X, Y) x₂}
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : PathOver y₁ y₂ p.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - induction p ; cbn in *.
    exact H.
  - apply PathOver_inConstantFamily.
    exact H.
  - induction p.
    induction x₁ as [x₁ | x₁].
    + exact (IHP₁ x₁ x₁ (idpath _) y₁ y₂ (ii1_injectivity H)).
    + exact (IHP₂ x₁ x₁ (idpath _) y₁ y₂ (ii2_injectivity H)).
  - induction p.
    specialize (IHP₁ (pr1 x₁) (pr1 x₁)
                     (idpath _)
                     (pr1 y₁) (pr1 y₂)
                     (maponpaths pr1 H)).    
    specialize (IHP₂ (pr2 x₁) (pr2 x₁)
                     (idpath _)
                     (pr2 y₁) (pr2 y₂)
                     (maponpaths dirprod_pr2 H)).
    exact (PathOver_pair IHP₁ IHP₂).
Defined.

Definition PathOver_poly_dact_const_idpath
           {P : poly_code}
           {X Y : one_type}
           {x : poly_act P X}
           (y : poly_dact_UU P (λ _ : X, Y) x)
  : PathOver_poly_dact_const
      (idpath x)
      (idpath _)
    =
    identityPathOver y.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (IHP₁ x y).
    + exact (IHP₂ x y).
  - exact (paths_pathsdirprod (IHP₁ _ (pr1 y)) (IHP₂ _ (pr2 y))).
Qed.

Definition inv_equality_cases
           {A B : UU}
           {x y : A ⨿ B}
           (p : equality_cases x y)
  : equality_cases y x.
Proof.
  induction x as [x | x], y as [y | y].
  - exact (!p).
  - exact (fromempty p).
  - exact (fromempty p).
  - exact (!p).
Defined.

Definition equality_by_cases_inv
           {A B : UU}
           {x y : A ⨿ B}
           (p : x = y)
  : equality_by_case (!p) = inv_equality_cases (equality_by_case p).
Proof.
  induction x as [x | x], y as [y | y], p
  ; apply idpath.
Defined.
  
Definition ii1_injectivity_inv
           {A B : UU}
           {x y : A}
           (p : @inl A B x = inl y)
  : ii1_injectivity (!p) = !(ii1_injectivity p).
Proof.
  exact (equality_by_cases_inv p).
Qed.

Definition ii2_injectivity_inv
           {A B : UU}
           {x y : B}
           (p : @inr A B x = inr y)
  : ii2_injectivity (!p) = !(ii2_injectivity p).
Proof.
  exact (equality_by_cases_inv p).
Qed.

Definition pathsdirprod_inversePathOver
           {P₁ P₂ : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a : poly_act (P₁ * P₂) A}
           {y₁ y₂ : poly_dact_UU (P₁ * P₂) Y a}
           (p : @PathOver
                  _ _ _
                  (poly_dact_UU P₁ Y)
                  (pr1 y₁) (pr1 y₂)
                  (idpath _))
           (q : @PathOver
                  _ _ _
                  (poly_dact_UU P₂ Y)
                  (pr2 y₁) (pr2 y₂)
                  (idpath _))
  : pathsdirprod
      (inversePathOver p)
      (inversePathOver q)
    =
    inversePathOver (PathOver_pair p q).
Proof.
  induction p, q.
  apply idpath.
Qed.
  
Definition PathOver_poly_dact_const_inverse
           {P : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P X}
           (p : x₁ = x₂)
           {y₁ : poly_dact_UU P (λ _ : X, Y) x₁}
           {y₂ : poly_dact_UU P (λ _ : X, Y) x₂}
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : PathOver_poly_dact_const
      (!p)
      (!H)
    =
    inversePathOver
      (PathOver_poly_dact_const
         p               
         H).
Proof.
  unfold PathOver_poly_dact_const_eq in H.
  induction p.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x₁ as [x | x].
    + simpl.
      refine (_ @ IHP₁ x y₁ y₂ (ii1_injectivity H)).
      apply maponpaths.
      apply ii1_injectivity_inv.
    + simpl.
      refine (_ @ IHP₂ x y₁ y₂ (ii2_injectivity H)).
      apply maponpaths.
      apply ii2_injectivity_inv.
  - specialize (IHP₁ _ _ _ (maponpaths pr1 H)).
    specialize (IHP₂ _ _ _ (maponpaths dirprod_pr2 H)).
    etrans.
    {
      simpl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (maponpathsinv0 dirprod_pr2 H).
      }
      apply IHP₂.
    }
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (maponpathsinv0 pr1 H).
      }
      apply IHP₁.
    }
    clear IHP₁ IHP₂.
    exact (pathsdirprod_inversePathOver _ _).
Qed.

Definition PathOver_poly_dact_const_concat
           {P : poly_code}
           {X Y : one_type}
           {x₁ x₂ x₃ : poly_act P X}
           (p₁ : x₁ = x₂) (p₂ : x₂ = x₃)
           {y₁ : poly_dact_UU P (λ _ : X, Y) x₁}
           {y₂ : poly_dact_UU P (λ _ : X, Y) x₂}
           {y₃ : poly_dact_UU P (λ _ : X, Y) x₃}
           (H₁ : PathOver_poly_dact_const_eq y₁ y₂)
           (H₂ : PathOver_poly_dact_const_eq y₂ y₃)
  : PathOver_poly_dact_const
      (p₁ @ p₂)
      (H₁ @ H₂)
    =
    composePathOver
      (PathOver_poly_dact_const p₁ H₁)
      (PathOver_poly_dact_const p₂ H₂).
Proof.
  induction p₁, p₂.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x₁ as [x | x].
    + simpl.
      refine (_ @ IHP₁ _ _ _ _ _ _).
      apply maponpaths.
      apply ii1_injectivity_concat.
    + simpl.
      refine (_ @ IHP₂ _ _ _ _ _ _).
      apply maponpaths.
      apply ii2_injectivity_concat.
  - simpl.
    refine (_ @ !(pathsdirprod_concat _ _ _ _)).
    apply paths_pathsdirprod.
    + refine (_ @ IHP₁ _ _ _ _ (maponpaths pr1 H₁) (maponpaths pr1 H₂)).
      apply maponpaths.
      exact (maponpathscomp0 pr1 H₁ H₂).
    + refine (_ @ IHP₂ _ _ _ _ (maponpaths dirprod_pr2 H₁) (maponpaths dirprod_pr2 H₂)).
      apply maponpaths.
      exact (maponpathscomp0 dirprod_pr2 H₁ H₂).
Qed.

Definition PathOver_poly_dact_const_pr1
           {P₁ P₂ : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P₁ X × poly_act P₂ X}
           (p : x₁ = x₂)
           {y₁ : poly_dact_UU (P₁ * P₂) (λ _ : X, Y) x₁}
           {y₂ : poly_dact_UU (P₁ * P₂) (λ _ : X, Y) x₂}
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : PathOver_poly_dact_const
      (maponpaths pr1 p)
      (maponpaths pr1 H)
    =
    PathOver_pr1
      (PathOver_poly_dact_const
         _
         H).
Proof.
  induction p.
  simpl.
  refine (!_).
  apply maponpaths_pr1_pathsdirprod.
Qed.

Definition PathOver_poly_dact_const_pr2
           {P₁ P₂ : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P₁ X × poly_act P₂ X}
           (p : x₁ = x₂)
           {y₁ : poly_dact_UU (P₁ * P₂) (λ _ : X, Y) x₁}
           {y₂ : poly_dact_UU (P₁ * P₂) (λ _ : X, Y) x₂}
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : PathOver_poly_dact_const
      (maponpaths dirprod_pr2 p)
      (maponpaths dirprod_pr2 H)
    =
    PathOver_pr2
      (PathOver_poly_dact_const
         _
         H).
Proof.
  induction p.
  simpl.
  refine (!_).
  apply maponpaths_pr2_pathsdirprod.
Qed.

Definition PathOver_cases
           {P₁ P₂ : poly_code}
           {A : UU}
           (Y : A → UU)
           {a₁ a₂ : poly_act (P₁ + P₂) A}
           (y₁ : poly_dact_UU (P₁ + P₂) Y a₁)
           (y₂ : poly_dact_UU (P₁ + P₂) Y a₂)
           (p : a₁ = a₂)
  : UU.
Proof.
  induction a₁ as [a₁ | a₁], a₂ as [a₂ | a₂].
  - exact (@PathOver _ _ _ (poly_dact_UU P₁ Y) y₁ y₂ (ii1_injectivity p)).
  - exact ∅.
  - exact ∅.
  - exact (@PathOver _ _ _ (poly_dact_UU P₂ Y) y₁ y₂ (ii2_injectivity p)).
Defined.

Definition PathOver_by_case
           {P₁ P₂ : poly_code}
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : poly_act (P₁ + P₂) A}
           {y₁ : poly_dact_UU (P₁ + P₂) Y a₁}
           {y₂ : poly_dact_UU (P₁ + P₂) Y a₂}
           {p : a₁ = a₂}
           (pp : PathOver y₁ y₂ p)
  : PathOver_cases Y y₁ y₂ p.
Proof.
  induction p.
  induction a₁ as [a | a].
  - exact pp.
  - exact pp.
Defined.



Definition PathOver_poly_dact_const_inv
           {P : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P X}
           (p : x₁ = x₂)
           (y₁ : poly_dact_UU P (λ _ : X, Y) x₁)
           (y₂ : poly_dact_UU P (λ _ : X, Y) x₂)
           (H : PathOver y₁ y₂ p)
  : PathOver_poly_dact_const_eq y₁ y₂.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - induction p.
    exact H.
  - unfold PathOver_poly_dact_const_eq ; cbn in * ; unfold idfun.
    exact (PathOver_const H).
  - induction x₁ as [x₁ | x₁], x₂ as [x₂ | x₂].
    + unfold PathOver_poly_dact_const_eq in *.
      simpl.
      refine (maponpaths inl _).
      apply (IHP₁ _ _ (ii1_injectivity p) _ _).
      exact (PathOver_by_case H).
    + induction (negpathsii1ii2 _ _ p).
    + induction (negpathsii2ii1 _ _ p).
    + unfold PathOver_poly_dact_const_eq in *.
      simpl.
      refine (maponpaths inr _).
      apply (IHP₂ _ _ (ii2_injectivity p) _ _).
      exact (PathOver_by_case H).
  - unfold PathOver_poly_dact_const_eq ; simpl.
    simple refine
           (pathsdirprod
              (IHP₁ _ _ (maponpaths pr1 p) _ _ _)
              (IHP₂ _ _ (maponpaths dirprod_pr2 p) _ _ _)).
    + exact (PathOver_pr1 H).
    + exact (PathOver_pr2 H).
Defined.

Definition PathOver_poly_dact_const_PathOver_poly_dact_const_inv
           {P : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P X}
           (p : x₁ = x₂)
           (y₁ : poly_dact_UU P (λ _ : X, Y) x₁)
           (y₂ : poly_dact_UU P (λ _ : X, Y) x₂)
           (H : PathOver y₁ y₂ p)
  : PathOver_poly_dact_const _ (PathOver_poly_dact_const_inv _ _ _ H) = H.
Proof.
  induction p.
  induction H.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x₁ as [x₁ | x₁].
    + simpl.
      refine (_ @ IHP₁ _ _).
      apply maponpaths.
      apply ii1_injectivity_inl.
    + simpl.
      refine (_ @ IHP₂ _ _).
      apply maponpaths.
      apply ii2_injectivity_inr.
  - simpl.
    refine (paths_pathsdirprod (_ @ IHP₁ _ (pr1 y₁)) (_ @ IHP₂ _ (pr2 y₁))).
    + apply maponpaths.
      apply maponpaths_pr1_pathsdirprod.
    + apply maponpaths.
      apply maponpaths_pr2_pathsdirprod.
Qed.

Definition path_PathOverPair
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ y₁ : poly_act P₁ X} {x₂ y₂ : poly_act P₂ X}
           {p : x₁ = y₁} {q : x₂ = y₂}
           {z₁ : poly_dact P₁ Y x₁} {z₁' : poly_dact P₁ Y y₁}
           {z₂ : poly_dact P₂ Y x₂} {z₂' : poly_dact P₂ Y y₂}
           {pp pp' : @PathOver _ _ _ (poly_dact P₁ Y) z₁ z₁' p}
           {qq qq' : @PathOver _ _ _ (poly_dact P₂ Y) z₂ z₂' q}
           (s₁ : pp = pp') (s₂ : qq = qq')
  : PathOver_pair pp qq = PathOver_pair pp' qq'.
Proof.
  induction s₁, s₂.
  apply idpath.
Qed.

Definition PathOver_pair_poly_dact_const
           {P₁ P₂ : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P₁ X}
           (p : x₁ = x₂)
           (y₁ : poly_dact_UU P₁ (λ _, Y) x₁)
           (y₂ : poly_dact_UU P₁ (λ _, Y) x₂)
           (H : PathOver_poly_dact_const_eq y₁ y₂)
           {x₁' x₂' : poly_act P₂ X}
           (p' : x₁' = x₂')
           (y₁' : poly_dact_UU P₂ (λ _, Y) x₁')
           (y₂' : poly_dact_UU P₂ (λ _, Y) x₂')
           (H' : PathOver_poly_dact_const_eq y₁' y₂')
  : PathOver_pair
      (PathOver_poly_dact_const p H)
      (PathOver_poly_dact_const p' H')
    =
    @PathOver_poly_dact_const
      (P₁ * P₂)
      X Y
      (x₁ ,, x₁')
      (x₂ ,, x₂')
      (pathsdirprod p p')
      (y₁ ,, y₁')
      (y₂ ,, y₂')
      (pathsdirprod H H').
Proof.
  induction p, p'.
  simpl.
  apply paths_pathsdirprod.
  - apply maponpaths.
    exact (!(maponpaths_pr1_pathsdirprod _) _).
  - apply maponpaths.
    exact (!(maponpaths_pr2_pathsdirprod _) _).
Qed.

Definition PathOver_inl_poly_dact_const
           {P₁ P₂ : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P₁ X}
           (p : x₁ = x₂)
           (y₁ : poly_dact_UU P₁ (λ _, Y) x₁)
           (y₂ : poly_dact_UU P₁ (λ _, Y) x₂)
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : PathOver_inl (PathOver_poly_dact_const p H)
    =
    @PathOver_poly_dact_const
      (P₁ + P₂)
      X Y
      (inl x₁) (inl x₂)
      (maponpaths inl p)
      _
      _
      (maponpaths inl H).
Proof.
  induction p.
  simpl.
  apply maponpaths.
  exact (!(ii1_injectivity_inl _)).
Qed.

Definition PathOver_inr_poly_dact_const
           {P₁ P₂ : poly_code}
           {X Y : one_type}
           {x₁ x₂ : poly_act P₂ X}
           (p : x₁ = x₂)
           (y₁ : poly_dact_UU P₂ (λ _, Y) x₁)
           (y₂ : poly_dact_UU P₂ (λ _, Y) x₂)
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : PathOver_inr (PathOver_poly_dact_const p H)
    =
    @PathOver_poly_dact_const
      (P₁ + P₂)
      X Y
      (inr x₁) (inr x₂)
      (maponpaths inr p)
      _
      _
      (maponpaths inr H).
Proof.
  induction p.
  simpl.
  apply maponpaths.
  exact (!(ii2_injectivity_inr _)).
Qed.

Definition apd_2_const_help
           {P : poly_code}
           {A B : one_type}
           {a : poly_act P A}
           {y₁ : poly_dact_UU P (λ _ : A, B) a}
           {y₂ : poly_dact_UU P (λ _ : A, B) a}
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : maponpaths
      (poly_dact_const P a)
      (PathOver_poly_dact_const (idpath a) H)
    =
    H.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply maponpathsidfun.
  - apply maponpathsidfun.
  - induction a as [a | a].
    + simpl.
      etrans.
      {
        refine (!_).
        apply maponpathscomp.
      }
      etrans.
      {
        apply maponpaths.
        exact (IHP₁ a y₁ y₂ (ii1_injectivity H)).
      }
      apply inl_ii1_injectivity.
    + simpl.
      etrans.
      {
        refine (!_).
        apply maponpathscomp.
      }
      etrans.
      {
        apply maponpaths.
        exact (IHP₂ a y₁ y₂ (ii2_injectivity H)).
      }
      apply inr_ii2_injectivity.
  - simpl.
    etrans.
    {
      refine (!_).
      apply maponpaths_pathsdirprod.
    }
    etrans.
    {
      exact (paths_pathsdirprod
               (IHP₁ _ _ _ (maponpaths pr1 H))
               (IHP₂ _ _ _ (maponpaths dirprod_pr2 H))).
    }
    exact (!(pathsdirprod_eta H)).
Qed.

Definition apd_2_const
           {P : poly_code}
           {A B : one_type}
           (cA : poly_act P A → A)
           (cB : poly_act P B → B)
           {a₁ a₂ : poly_act P A}
           (p : a₁ = a₂)
           {y₁ : poly_dact_UU P (λ _ : A, B) a₁}
           {y₂ : poly_dact_UU P (λ _ : A, B) a₂}
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : @apd_2
      (poly_act P A) A
      (poly_dact P (λ _, B)) (λ _, B)
      cA
      (λ x z, cB (poly_dact_const P x z))
      _ _
      p
      y₁ y₂
      (PathOver_poly_dact_const p H)
    =
    PathOver_inConstantFamily
      (maponpaths cA p)
      (maponpaths cB H).
Proof.
  induction p.
  simpl.
  etrans.
  {
    refine (!_).
    apply maponpathscomp.
  }
  apply maponpaths.
  apply apd_2_const_help.
Qed.

Definition apd_2_endpoint_dact
           {W P Q : poly_code}
           (e : endpoint W P Q)
           {A B : one_type}
           (cA : poly_act W A → A)
           (cB : poly_act W B → B)
           {a₁ a₂ : poly_act P A}
           (p : a₁ = a₂)
           {y₁ : poly_dact_UU P (λ _ : A, B) a₁}
           {y₂ : poly_dact_UU P (λ _ : A, B) a₂}
           (H : PathOver_poly_dact_const_eq y₁ y₂)
  : @apd_2
      (poly_act P A) (poly_act Q A)
      (poly_dact P (λ _, B)) (poly_dact Q (λ _, B))
      (sem_endpoint_one_types e (A ,, cA))
      (@endpoint_dact
         _ (A ,, cA) (λ _, B)
         _ _
         e
         (λ _ x, cB (poly_dact_const _ _ x)))
      _ _
      p
      y₁ y₂
      (PathOver_poly_dact_const p H)
    =
    PathOver_poly_dact_const
      _
      (endpoint_dact_const (_ ,, cA) (_ ,, cB) e _
       @ maponpaths (sem_endpoint_UU e cB) H
       @ !(endpoint_dact_const (_ ,, cA) (_ ,, cB) e _)).
Proof.
  induction p.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ].
  - simpl.
    etrans.
    {
      apply maponpathsidfun.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpathsidfun.
  - simpl ; unfold dep_comp_fun ; simpl in *.
    etrans.
    {
      refine (!_).
      apply maponpathscomp.
    }
    etrans.
    {
      apply maponpaths.
      apply IHe₁.
    }
    etrans.
    {
      apply IHe₂.
    }
    clear IHe₁ IHe₂.
    apply maponpaths.
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply pathscomp_inv.
    }
    do 2 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths.
      apply maponpathscomp0.
    }
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp.
    }
    apply maponpaths.
    apply maponpathsinv0.
  - simpl.
    etrans.
    {
      apply maponpathsidfun.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply pathscomp0rid.
    }
    apply ii1_injectivity_inl.
  - simpl.
    etrans.
    {
      apply maponpathsidfun.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply pathscomp0rid.
    }
    apply ii2_injectivity_inr.
  - simpl.
    etrans.
    {
      apply maponpaths_pr1_pathsdirprod.
    }
    apply maponpaths.
    refine (!_).
    apply pathscomp0rid.
  - simpl.
    etrans.
    {
      apply maponpaths_pr2_pathsdirprod.
    }
    apply maponpaths.
    refine (!_).
    apply pathscomp0rid.
  - simpl.
    etrans.
    {
      apply maponpaths_prod_path.
    }
    apply paths_pathsdirprod.
    + refine (IHe₁ _ _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths_prod_path.
          }
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      apply maponpaths_pr1_pathsdirprod.
    + refine (IHe₂ _ _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths_prod_path.
          }
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      apply maponpaths_pr2_pathsdirprod.
  - simpl.
    etrans.
    {
      apply maponpaths_for_constant_function.
    }
    refine (!_).
    etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpaths_for_constant_function.
  - simpl.
    refine (!_).
    apply pathscomp0rid.
  - simpl.
    refine (_ @ !(pathscomp0rid _)).
    exact (apd_2_const cA cB (idpath _) H).
Qed.

Section ConstantDispAlgebra.
  Context {Σ : hit_signature}
          (X Y : hit_algebra_one_types Σ).

  Definition const_disp_algebra_fam
    : alg_carrier X → one_type
    := λ _, pr111 Y.

  Definition const_disp_algebra_constr
    : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
      poly_dact (point_constr Σ) const_disp_algebra_fam x
      →
      const_disp_algebra_fam (alg_constr X x)
    := λ x z, alg_constr Y (poly_dact_const (point_constr Σ) x z).

  Definition const_disp_algebra_PathOver
    : ∏ (j : path_label Σ)
        (x : poly_act (path_source Σ j) (alg_carrier X))
        (y : poly_dact (path_source Σ j) const_disp_algebra_fam x),
      @PathOver
        _ _ _
        const_disp_algebra_fam
        (endpoint_dact
           (pr11 X) _ (path_left Σ j) const_disp_algebra_constr y)
        (endpoint_dact
           (pr11 X) _ (path_right Σ j) const_disp_algebra_constr y)
        (alg_path X j x)
    := λ j x z,
       PathOver_inConstantFamily
         (alg_path X j x)
         ((endpoint_dact_const _ _ (path_left Σ j) z)
            @ alg_path Y j (poly_dact_const (path_source Σ j) x z)
            @ !(endpoint_dact_const _ _ (path_right Σ j) z)).

  Definition homot_endpoint_dact_const
             {Q : poly_code}
             {TR : poly_code}
             {al ar : endpoint _ Q TR}
             {T : poly_code}
             {sl sr : endpoint _ Q T}
             (p : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
             {z : poly_act Q (pr111 X : one_type)}
             (zz : poly_dact_UU Q (λ _, alg_carrier Y) z)
             {p_arg : sem_endpoint_one_types al _ z = sem_endpoint_one_types ar _ z}
             (pp_arg : @PathOver
                         _ _ _
                         (poly_dact_UU TR (λ _, alg_carrier Y))
                         (endpoint_dact
                            (pr11 X)
                            (λ _, pr111 Y)
                            al
                            const_disp_algebra_constr
                            zz)
                         (endpoint_dact
                            (pr11 X)
                            (λ _, pr111 Y)
                            ar
                            const_disp_algebra_constr
                            zz)
                         (sem_homot_endpoint_one_types
                            path_arg
                            (pr11 X) (pr21 X)
                            z p_arg))
    : homot_endpoint_dact p _ const_disp_algebra_PathOver zz pp_arg
      =
      PathOver_poly_dact_const
        (sem_homot_endpoint_one_types p (pr11 X) (pr21 X) z p_arg)
        (endpoint_dact_const _ _ _ _
         @ sem_homot_endpoint_one_types
             p (pr11 Y) (pr21 Y)
             (poly_dact_const _ z zz)
             (!(endpoint_dact_const _ _ _ _)
              @ PathOver_poly_dact_const_inv _ _ _ pp_arg
              @ endpoint_dact_const _ _ _ _)
         @ !(endpoint_dact_const _ _ _ _)).
  Proof.
    refine (!_).
    induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                    | T₁ T₂ e₁ e₂ e₃ h IHh
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | P R e₁ e₂ | P R e₁ e₂
                    | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                    | P₁ P₂ P₃ e₁ e₂ e₃
                    | Z x T e | j e | ].
    - simpl.
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      exact (PathOver_poly_dact_const_idpath _).
    - simpl.
      refine (_ @ maponpaths _ IHp).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          exact (!(pathsinv0inv0 _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (!(pathscomp_inv _ _)).
        }
        exact (!(pathscomp_inv _ _)).
      }
      etrans.
      {
        exact (PathOver_poly_dact_const_inverse _ _).
      }
      do 2 apply maponpaths.
      exact (!(path_assoc _ _ _)).
    - simpl.
      refine (_ @ maponpaths (composePathOver _) IHP₂).
      refine (_ @ maponpaths (λ z, composePathOver z _) IHP₁).
      refine (_ @ PathOver_poly_dact_const_concat _ _ _ _).
      apply maponpaths.
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
      apply maponpaths.
      do 2 refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply pathsinv0l.
      }
      apply idpath.
    - simpl.
      refine (_ @ maponpaths _ IHh) ; clear IHh.
      refine (!_).
      etrans.
      {
        apply (apd_2_endpoint_dact e₃).
      }
      apply maponpaths.
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply pathscomp_inv.
      }
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (maponpathscomp0 (sem_endpoint_one_types e₃ (pr11 Y))).
        }
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (maponpathsinv0 (sem_endpoint_one_types e₃ (pr11 Y))).
        }
        refine (!_).
        apply (maponpathscomp0 (sem_endpoint_one_types e₃ (pr11 Y))).
      }
      apply maponpaths.
      refine (!_).
      apply path_assoc.
    - simpl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          refine (!(path_assoc _ _ _) @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (maponpathscomp (sem_endpoint_UU e₂ _) (sem_endpoint_UU e₃ (pr211 Y))).
          }
          refine (!_).          
          apply (maponpathscomp0 (sem_endpoint_UU e₃ (pr211 Y))).
        }
        apply pathsinv0r.
      }
      exact (PathOver_poly_dact_const_idpath _).
    - simpl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply pathscomp0rid.
        }
        apply pathsinv0r.
      }
      exact (PathOver_poly_dact_const_idpath _).
    - simpl.
      etrans.
      {
        apply maponpaths.
        cbn.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathsidfun.
        }
        apply pathsinv0r.
      }
      exact (PathOver_poly_dact_const_idpath _).
    - simpl.
      etrans.
      {
        apply maponpaths.
        cbn.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths_pr1_pathsdirprod.
        }
        apply pathsinv0r.
      }
      exact (PathOver_poly_dact_const_idpath _).
    - simpl.
      etrans.
      {
        apply maponpaths.
        cbn.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths_pr2_pathsdirprod.
        }
        apply pathsinv0r.
      }
      exact (PathOver_poly_dact_const_idpath _).
    - refine (_ @ path_PathOverPair IHp₁ IHp₂).
      refine (_ @ !(PathOver_pair_poly_dact_const _ _ _ _ _ _ _ _)).
      apply maponpaths.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      apply idpath.
    - simpl.
      refine (paths_pathsdirprod _ _ @ _).
      + etrans.
        {
          apply maponpaths.
          etrans.
          {
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  cbn.
                  apply maponpaths_prod_path.
                }
                apply pathsdirprod_concat.
              }
              etrans.
              {
                apply maponpaths.
                apply pathsdirprod_inv.
              }
              apply pathsdirprod_concat.
            }
            apply maponpaths_pr1_pathsdirprod.
          }
          apply pathsinv0r.
        }
        exact (PathOver_poly_dact_const_idpath _).
      + etrans.
        {
          apply maponpaths.
          etrans.
          {
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths_2.
                etrans.
                {
                  apply maponpaths.
                  cbn.
                  apply maponpaths_prod_path.
                }
                apply pathsdirprod_concat.
              }
              etrans.
              {
                apply maponpaths.
                apply pathsdirprod_inv.
              }
              apply pathsdirprod_concat.
            }
            apply maponpaths_pr2_pathsdirprod.
          }
          apply pathsinv0r.
        }
        exact (PathOver_poly_dact_const_idpath _).
      + apply idpath.
    - simpl.
      cbn.
      etrans.
      {        
        apply pathscomp0rid.
      }
      apply maponpaths_for_constant_function.
    - simpl.
      unfold const_disp_algebra_PathOver.
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        apply pathscomp_inv.
      }
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (maponpathsinv0 (sem_endpoint_one_types (path_right Σ j) (pr11 Y))).
      }
      refine (!(path_assoc _ _ _) @ _).
      refine (!_).
      etrans.
      {
        exact (homotsec_natural
                 (alg_path Y j)
                 (!endpoint_dact_const (pr11 X) (pr11 Y) e zz)).
      }
      refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
      do 2 apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0inv0.
    - simpl.
      etrans.
      {
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          do 2 refine (path_assoc _ _ _ @ _).
          do 2 apply maponpaths_2.
          apply pathsinv0r.
        }
        simpl.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          apply pathsinv0r.
        }
        apply pathscomp0rid.
      }
      exact (PathOver_poly_dact_const_PathOver_poly_dact_const_inv
               p_arg
               _ _
               pp_arg).
  Qed.
  
  Definition const_disp_algebra_globe_over
             (j : homot_label Σ)
             (z : poly_act
                    (homot_point_arg Σ j)
                    (alg_carrier X))
             (zz : poly_dact_UU
                     (homot_point_arg Σ j)
                     (const_disp_algebra_fam)
                     z)
             (p : sem_endpoint_one_types
                    (homot_path_arg_left Σ j)
                    (pr11 X)
                    z
                  =
                  sem_endpoint_one_types
                    (homot_path_arg_right Σ j)
                    (pr11 X)
                    z)
             (pp : @PathOver
                     _ _ _
                     (poly_dact
                        (homot_path_arg_target Σ j)
                        const_disp_algebra_fam)
                     (endpoint_dact
                        (pr11 X)
                        const_disp_algebra_fam
                        (homot_path_arg_left Σ j)
                        const_disp_algebra_constr zz)
                     (endpoint_dact
                        (pr11 X)
                        const_disp_algebra_fam
                        (homot_path_arg_right Σ j)
                        const_disp_algebra_constr zz)
                     (sem_homot_endpoint_one_types
                        path_arg (pr11 X)
                        (pr21 X)
                        z p))
    : globe_over
        (const_disp_algebra_fam)
        (pr2 X j z p)
        (homot_endpoint_dact
           (homot_left_path Σ j)
           const_disp_algebra_constr
           const_disp_algebra_PathOver
           zz pp)
        (homot_endpoint_dact
           (homot_right_path Σ j)
           const_disp_algebra_constr
           const_disp_algebra_PathOver
           zz pp).
  Proof.
    unfold const_disp_algebra_fam.
    simpl.
    simple refine
           (globe_over_whisker
              _
              _
              (!(homot_endpoint_dact_const
                   (homot_left_path Σ j)
                   zz
                   pp))
              (!(homot_endpoint_dact_const
                   (homot_right_path Σ j)
                   zz
                   pp))
              (const_globe_over
                 _ _
                 _ _)).
    unfold globe.
    apply maponpaths.
    apply maponpaths_2.
    apply (alg_homot Y).
  Qed.

  Definition const_disp_algebra
    : disp_algebra X.
  Proof.
    use make_disp_algebra.
    - exact const_disp_algebra_fam.
    - exact const_disp_algebra_constr.
    - exact const_disp_algebra_PathOver.
    - exact const_disp_algebra_globe_over.
  Defined.
End ConstantDispAlgebra.

Definition const_PathOver_square
           {X Y : UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y} {y₂ : Y} 
           {y₁' : Y} {y₂' : Y} 
           {q : PathOver y₁ y₂ p}
           {q' : PathOver y₁' y₂' p}
           {l : y₁ = y₁'} {r : y₂ = y₂'}
           (s : PathOver_square
                  (λ (x : X), Y)
                  (idpath _)
                  q q'
                  l
                  r)
  : PathOver_const q @ r = l @ PathOver_const q'.
Proof.
  induction l, r, p ; simpl in *.
  exact (pathscomp0rid _ @ s).
Defined.

Definition PathOver_const_apd
           {X Y : UU}
           (f : X → Y)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
  : PathOver_const (apd f p) = maponpaths f p.
Proof.
  induction p.
  apply idpath.
Defined.

Definition endpoint_dact_natural_const
           (Σ : hit_signature)
           {P Q : poly_code}
           (e : endpoint (point_constr Σ) P Q)
           {X Y : hit_algebra_one_types Σ}
           {f : disp_algebra_map (const_disp_algebra X Y)}
           (x : poly_act P (pr111 X : one_type))
  : !(poly_dmap_const Q _ (pr1 f))
    @ maponpaths
        (poly_dact_const _ _)
        (endpoint_dact_natural
           e
           (pr12 f)
           x)
    @ endpoint_dact_const
        (pr11 X)
        (pr11 Y)
        e
        (poly_dmap P (const_disp_algebra_fam X Y) (pr1 f) x)
    @ maponpaths
        (sem_endpoint_UU e (alg_constr Y))
        (poly_dmap_const _ _ _)
    =
    sem_endpoint_UU_natural
        e
        (λ z, pr12 f z
                   @ maponpaths (alg_constr Y) (poly_dmap_const _ z (pr1 f)))
        x.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - simpl.
    etrans.
    {
      apply maponpaths.
      apply maponpathsidfun.
    }
    apply pathsinv0l.
  - simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply IHe₂.
    }
    clear IHe₂.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply IHe₁.
    }
    clear IHe₁.
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      apply maponpathscomp.
    }
    do 3 refine (path_assoc _ _ _ @ _).
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    do 2 refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply (maponpathscomp
               (endpoint_dact
                  (pr11 X)
                  (const_disp_algebra_fam X Y)
                  e₂
                  (disp_alg_constr (const_disp_algebra X Y)))).
    }
    etrans.
    {
      exact (homotsec_natural'
               (endpoint_dact_const (pr11 X) (pr11 Y) e₂)
               (endpoint_dact_natural e₁ (pr12 f) x)).
    }
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathscomp0.
      }
      refine (!_).
      apply maponpathscomp0.
    }
    refine (!_).
    etrans.
    {
      refine (!_).
      apply maponpathscomp.
    }    
    apply maponpaths.
    refine (!(pathscomp0lid _) @ _).
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    exact (!(pathsinv0r _)).
  - apply pathsinv0l.
  - apply pathsinv0l.
  - simpl.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_pr1_pathsdirprod.
    }
    apply pathsinv0l.
  - simpl.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_pr2_pathsdirprod.
    }
    apply pathsinv0l.
  - simpl.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        apply pathsdirprod_inv.
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_prod_path.
          }
          apply pathsdirprod_concat.
        }
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply maponpaths_pathsdirprod.
        }
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    exact (paths_pathsdirprod (IHe₁ _) (IHe₂ _)).
  - apply maponpaths_for_constant_function.
  - apply idpath.
  - simpl.
    apply maponpaths_2.
    apply maponpathsidfun.
Qed.

Definition const_disp_alg_mor_to_alg_mor_help
           {Σ : hit_signature}
           (X Y : hit_algebra_one_types Σ)
           (f : disp_algebra_map (const_disp_algebra X Y))
           (i : path_label Σ)
           (x : poly_act (path_source Σ i) (path_alg_carrier (pr1 X)))
  : maponpaths (pr1 f) ((pr21 X) i x)
  @ sem_endpoint_UU_natural (path_right Σ i)
      (λ x,
       (pr12 f) x
        @ maponpaths (pr211 Y) (poly_dmap_const (point_constr Σ) x (pr1 f)))
      x
  =
  sem_endpoint_UU_natural
    (path_left Σ i)
    (λ x,
     (pr12 f) x
      @ maponpaths (pr211 Y) (poly_dmap_const (point_constr Σ) x (pr1 f)))
    x
    @ (pr21 Y) i (poly_map (path_source Σ i) (pr1 f) x).
Proof.
  pose (pr22 f i x) as p.
  pose (const_PathOver_square p) as p'.
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply PathOver_const_apd.
  }
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply (endpoint_dact_natural_const Σ (path_right Σ i)).
  }
  simpl.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply maponpathsidfun.
  }
  refine (path_assoc _ _ _ @ _).
  etrans.
  {
    apply maponpaths_2.
    exact p'.
  }
  clear p p'.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply (endpoint_dact_natural_const Σ (path_left Σ i)).
  }
  simpl.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply maponpathsidfun.
  }
  refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
  apply maponpaths.
  refine (!(path_assoc _ _ _) @ _).
  etrans.
  {
    apply maponpaths.
    exact (homotsec_natural'
             (pr21 Y i)
             (poly_dmap_const (path_source Σ i) x (pr1 f))).
  }
  refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
  apply maponpaths_2.
  unfold const_disp_algebra_fam.
  simpl.
  refine (!_).
  etrans.
  {
    unfold disp_alg_path.
    simpl.
    unfold const_disp_algebra_PathOver.
    apply maponpaths_2.
    apply (homotweqinvweq
             (make_weq
                _
                path_over_const_isweq)
             (endpoint_dact_const
                (pr11 X) (pr11 Y) (path_left Σ i)
                (poly_dmap (path_source Σ i) _ (pr1 f) x) @
                alg_path Y i
                (poly_dact_const
                   (path_source Σ i) x
                   (poly_dmap (path_source Σ i) _ (pr1 f) x)) @
                ! endpoint_dact_const (pr11 X) (pr11 Y) (path_right Σ i)
                (poly_dmap (path_source Σ i) _ (pr1 f) x))).
  }
  refine (!(path_assoc _ _ _) @ _).
  apply maponpaths.
  refine (!(path_assoc _ _ _) @ _).
  refine (_ @ pathscomp0rid _).
  apply maponpaths.
  apply pathsinv0l.
Qed.

Definition const_disp_alg_mor_to_alg_mor
           {Σ : hit_signature}
           (X Y : hit_algebra_one_types Σ)
  : disp_algebra_map (const_disp_algebra X Y) → X --> Y.
Proof.
  intros f.
  use make_algebra_map.
  use make_hit_path_alg_map ; simpl.
  - refine (pr1 f ,, _).
    use make_invertible_2cell.
    + intro.
      cbn.
      refine (pr12 f x @ _).
      cbn.
      unfold const_disp_algebra_constr.
      apply maponpaths.
      apply poly_dmap_const.
    + apply one_type_2cell_iso.
  - exact (const_disp_alg_mor_to_alg_mor_help _ _ f).
Defined.
