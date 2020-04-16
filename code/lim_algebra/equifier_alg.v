Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.globe_over_lem.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

Definition poly_dact_UU_on_homot
           {P : poly_code}
           {A B : UU}
           {f g : A → B}
           {p q : f ~ g}
           (x : poly_act P A)
           (Hx : poly_dact_UU P (λ z, p z = q z) x)
  : poly_homot P p x = poly_homot P q x.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact Hx.
  - induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (IHP₁ x Hx)).
    + exact (maponpaths (maponpaths inr) (IHP₂ x Hx)).
  - refine (maponpaths (pathsdirprod (poly_homot P₁ p (pr1 x))) (IHP₂ _ (pr2 Hx)) @ _).
    exact (maponpaths (λ z,  pathsdirprod z (poly_homot P₂ q (pr2 x))) (IHP₁ _ (pr1 Hx))). 
Defined.

Definition TODO {A : UU} : A.
Admitted.

Section Equifier.
  Context {Σ : hit_signature}
          {A B : hit_algebra_one_types Σ}
          {f g : A --> B}
          (p q : f ==> g).

  Definition equifier_disp_alg_constr
             (x : poly_act (point_constr Σ) (alg_carrier A))
             (Hx : poly_dact_UU
                     (point_constr Σ)
                     (λ a : alg_carrier A, alg_2cell_carrier p a = alg_2cell_carrier q a)
                     x)
    : alg_2cell_carrier p (alg_constr A x) = alg_2cell_carrier q (alg_constr A x).
  Proof.
    refine (!(pathscomp0rid _) @ _).
    refine (maponpaths (λ z, alg_2cell_carrier p (alg_constr A x) @ z)
                       (!(pathsinv0r (alg_map_commute g x))) @ _).
    refine (path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, z @ ! alg_map_commute g x) (alg_2cell_commute p x) @ _).
    refine (! path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, alg_map_commute f x
                                             @ maponpaths (alg_constr B) z
                                             @ ! alg_map_commute g x)
                       (poly_dact_UU_on_homot x Hx) @ _).
    refine (path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, z @ ! alg_map_commute g x) (! alg_2cell_commute q x) @ _).
    refine (! path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, alg_2cell_carrier q (alg_constr A x) @ z)
                       (pathsinv0r (alg_map_commute g x)) @ _).
    exact (pathscomp0rid _).
  Qed.
  
  Definition equifier_disp_alg
    : disp_algebra A.
  Proof.
    use prop_disp_algebra.
    - exact (λ a, alg_2cell_carrier p a = alg_2cell_carrier q a).
    - abstract (intro a ; exact (one_type_isofhlevel _ _ _ _ _)).
    - exact equifier_disp_alg_constr.
  Defined.

  Definition equifier
    : hit_algebra_one_types Σ
    := total_algebra equifier_disp_alg.

  Definition equifier_pr
    : equifier --> A
    := projection _.

  Definition equifier_homot_component
    : alg_2cell_carrier (equifier_pr ◃ p) ~ alg_2cell_carrier (equifier_pr ◃ q).
  Proof.
    exact pr2.
  Qed.

  Definition equifier_homot
    : equifier_pr ◃ p = equifier_pr ◃ q.
  Proof.
    use algebra_2cell_eq.
    exact equifier_homot_component.
  Qed.
  
End Equifier.


