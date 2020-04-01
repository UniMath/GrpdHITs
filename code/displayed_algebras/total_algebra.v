Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
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
Require Import displayed_algebras.globe_over_lem.

Local Open Scope cat.

Definition total2_one_type
           {X : one_type}
           (Y : X → one_type)
  : one_type.
Proof.
  use make_one_type.
  - exact (total2 Y).
  - use isofhleveltotal2.
    + apply X.
    + intro ; apply Y.
Defined.

(**
We first look at the first and second projection of a polynomial applied to a total type
 *)
Definition poly_pr1
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
  : poly_act P (total2_one_type Y) → poly_act P X
  := poly_map P pr1.

Definition poly_pr2
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
  : ∏ (x : poly_act P (total2_one_type Y)), poly_dact P Y (poly_pr1 P x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl in *.
  - exact (λ x, x).
  - exact (λ x, pr2 x).
  - induction x as [x | x] ; simpl.
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - intros x.
    refine (_ ,, _).
    + exact (IHP₁ (pr1 x)).
    + exact (IHP₂ (pr2 x)).
Defined.

Definition PathOver_poly_pr2
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
           {x y : poly_act P (∑ z, Y z)}
           (p : x = y)
  : @PathOver
      _ _ _
      (poly_dact P Y)
      (poly_pr2 P x)
      (poly_pr2 P y)
      (maponpaths (poly_pr1 _) p).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl in *.
  - induction p.
    apply idpath.
  - apply TotalPathToPathOver.
  - induction p ; apply idpath.
  - induction p ; apply idpath.
Defined.

Definition PathOver_poly_pr2_is_idpath
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
           (x : poly_act P (∑ z, Y z))
  : PathOver_poly_pr2 P (idpath x) = idpath _.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; apply idpath.
Qed.

Definition PathOver_poly_pr2_is_idpath_globe
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
           (x : poly_act P (∑ z, Y z))
  : globe_over
      (poly_dact P Y)
      (idpath _)
      (PathOver_poly_pr2 P (idpath x))
      (identityPathOver _).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; apply idpath.
Qed.

Definition PathOver_pr1_PathOver_poly_pr2
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {z₁ z₂ : poly_act (P₁ * P₂) (∑ z : X, Y z)}
           (p : z₁ = z₂)
  : globe_over
      (poly_dact _ Y)
      (maponpathscomp pr1 (poly_map P₁ pr1) p
       @ !(maponpathscomp (dirprodf (poly_map P₁ pr1) (poly_map P₂ pr1)) pr1 p))
      (PathOver_poly_pr2 P₁ (maponpaths pr1 p))
      (PathOver_pr1 (PathOver_poly_pr2 (P₁ * P₂) p)).
Proof.
  induction p.
  exact (PathOver_poly_pr2_is_idpath _ _).
Qed.

Definition PathOver_pr2_PathOver_poly_pr2
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {z₁ z₂ : poly_act (P₁ * P₂) (∑ z : X, Y z)}
           (p : z₁ = z₂)
  : globe_over
      (poly_dact _ Y)
      (maponpathscomp dirprod_pr2 (poly_pr1 P₂) p
       @ !(maponpathscomp (poly_pr1 (P₁ * P₂)) dirprod_pr2 p))
      (PathOver_poly_pr2 P₂ (maponpaths dirprod_pr2 p))
      (PathOver_pr2 (PathOver_poly_pr2 (P₁ * P₂) p)).
Proof.
  induction p.
  exact (PathOver_poly_pr2_is_idpath _ _).
Qed.

Definition PathOver_pr1_PathOver_poly_inl
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {z₁ z₂ : poly_act P₁ (∑ z : X, Y z)}
           (p : z₁ = z₂)
  : globe_over
      (poly_dact (P₁ + P₂) Y)
      (coprodf_path_maponpaths_inl (poly_pr1 P₁) (poly_pr1 P₂) p)
      (PathOver_poly_pr2 (P₁ + P₂) (maponpaths inl p))
      (PathOver_inl (PathOver_poly_pr2 P₁ p)).
Proof.
  induction p.
  exact (!(PathOver_poly_pr2_is_idpath _ _)).
Qed.

Definition PathOver_pr1_PathOver_poly_inr
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {z₁ z₂ : poly_act P₂ (∑ z : X, Y z)}
           (p : z₁ = z₂)
  : globe_over
      (poly_dact (P₁ + P₂) Y)
      (coprodf_path_maponpaths_inr (poly_pr1 P₁) (poly_pr1 P₂) p)
      (PathOver_poly_pr2 (P₁ + P₂) (maponpaths inr p))
      (PathOver_inr (PathOver_poly_pr2 P₂ p)).
Proof.
  induction p.
  exact (!(PathOver_poly_pr2_is_idpath _ _)).
Qed.

Definition PathOver_pr1_PathOver_poly_inv
           {P : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x y : poly_act P (∑ z : X, Y z)}
           (p : x = y)
  : globe_over
      (poly_dact P Y)
      (maponpathsinv0 _ _)
      (PathOver_poly_pr2 P (!p))
      (inversePathOver (PathOver_poly_pr2 P p)).
Proof.
  induction p.
  induction P ; apply idpath.
Qed.

Definition PathOver_pr1_PathOver_poly_concat
           {P : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x y z : poly_act P (∑ z : X, Y z)}
           (p : x = y) (q : y = z)
  : globe_over
      (poly_dact P Y)
      (maponpathscomp0 (poly_pr1 P) p q)
      (PathOver_poly_pr2 P (p @ q))
      (composePathOver
         (PathOver_poly_pr2 P p)
         (PathOver_poly_pr2 P q)).
Proof.
  induction p, q.
  unfold globe_over.
  simpl.
  cbn.
  unfold idfun.
  refine (!(pathscomp0rid _) @ !_).
  apply maponpaths.
  exact (PathOver_poly_pr2_is_idpath _ _).
Qed.

Definition PathOver_pr2_PathOver_pair
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ (∑ z : X, Y z)}
           {y₁ y₂ : poly_act P₂ (∑ z : X, Y z)}
           (p : x₁ = x₂) (q : y₁ = y₂)
  : globe_over
      (poly_dact (P₁ * P₂) Y)
      (!(maponpaths_pathsdirprod _ _ _ _))
      (PathOver_poly_pr2 (P₁ * P₂) (pathsdirprod p q))
      (PathOver_pair
         (PathOver_poly_pr2 P₁ p)
         (PathOver_poly_pr2 P₂ q)).
Proof.
  induction p, q.
  exact (!(paths_pathsdirprod
             (PathOver_poly_pr2_is_idpath _ _)
             (PathOver_poly_pr2_is_idpath _ _))).
Qed.

(**
Now we define the total algebra
 *)
Section TotalAlgebra.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}.
  Variable (Y : disp_algebra X).

  Local Definition carrier
    : one_type
    := total2_one_type (pr1 Y).

  Local Definition operation
    : poly_act (point_constr Σ) carrier → carrier
    := λ x,
       ((alg_constr X (poly_pr1 (point_constr Σ) x))
          ,,
          disp_alg_constr Y (poly_pr1 (point_constr Σ) x) (poly_pr2 (point_constr Σ) x)).

  Local Definition total_prealgebra
    : hit_prealgebra_one_types Σ.
  Proof.
    use tpair.
    - exact carrier.
    - exact operation.
  Defined.

  (** For the paths, we first need to look at the first and second projections of endpoints *)
  Local Definition pr1_endpoint
        {P Q : poly_code}
        (e : endpoint (point_constr Σ) P Q)
        (x : poly_act P carrier)
    : sem_endpoint_UU e (alg_constr X) (poly_pr1 P x)
      =
      poly_pr1 Q (sem_endpoint_UU e operation x).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ]
    ; try (apply idpath).
    - exact (maponpaths _ (IHe₁ _) @ IHe₂ _).
    - exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  Defined.

  Local Definition pr2_endpoint
        {P Q : poly_code}
        (e : endpoint (point_constr Σ) P Q)
        (x : poly_act P carrier)
    : @PathOver
        _ _ _
        (poly_dact Q (pr1 Y))
        (endpoint_dact _ _ e (disp_alg_constr Y) (poly_pr2 P x))
        (poly_pr2 Q (sem_endpoint_UU e operation x))
        (pr1_endpoint e _).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ].
    - apply idpath.
    - simpl.
      refine
        (composePathOver
           _
           (IHe₂ _)).
      exact (@apd_2
              _
              (poly_act R (path_alg_carrier (pr1 X)))
              _
              (poly_dact R (pr1 Y))
              _
              (λ _, endpoint_dact (pr11 X) (pr1 Y) e₂ (disp_alg_constr Y))
              _ _
              _
              _ _
              (IHe₁ x)
            ).
    - apply idpath.
    - apply idpath.
    - apply idpath.
    - apply idpath.
    - exact (PathOver_pair
               (IHe₁ x)
               (IHe₂ x)).
    - apply idpath.
    - apply idpath.
    - apply idpath.
  Defined.
  
  Local Definition paths
        (j : path_label Σ)
        (x : poly_act (path_source Σ j) carrier)
    : sem_endpoint_UU (path_left Σ j) operation x
      =
      sem_endpoint_UU (path_right Σ j) operation x.
  Proof.
    use PathOverToTotalPath'.
    - refine (!(pr1_endpoint (path_left Σ j) x) @ _ @ pr1_endpoint (path_right Σ j) x).
      exact (alg_path X j (poly_pr1 (path_source Σ j) x)).
    - exact
        (composePathOver
           (inversePathOver (pr2_endpoint (path_left Σ j) x))
           (composePathOver
              (disp_alg_path
                 Y j
                 (poly_pr1 (path_source Σ j) x)
                 _)
              (pr2_endpoint (path_right Σ j) x))).
  Defined.

  Definition TODO {A : UU} : A.
  Admitted.
  
  Local Definition pr1_homot_endpoint
        {Q : poly_code}
        {TR : poly_code}
        {al ar : endpoint (point_constr Σ) Q TR}
        {T : poly_code}
        {sl sr : endpoint (point_constr Σ) Q T}
        (h : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
        (x : poly_act
               Q
               (∑ x, pr1 Y x))
        (p : sem_endpoint_UU al operation x
             =
             sem_endpoint_UU ar operation x)
    : maponpaths
        (poly_pr1 _)
        (sem_homot_endpoint_UU
           h
           (∑ z, pr1 Y z)
           operation paths
           x p)
      =
      !(pr1_endpoint _ _)
       @ sem_homot_endpoint_UU
           h
           (alg_carrier X)
           (alg_constr X)
           (alg_path X)
           (poly_pr1 _ x)
           (pr1_endpoint _ _
            @ maponpaths (poly_pr1 _) p
            @ !(pr1_endpoint _ _))
       @ pr1_endpoint _ _.
  Proof.
    induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ e₃
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | P R e₁ e₂ | P R e₁ e₂
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | P₁ P₂ P₃ e₁ e₂ e₃
                    | W w T e
                    | j e | ].
    - (* identity *)
      exact (!pathsinv0l _).
    - (* symmetry *)
      simpl.
      refine (maponpathsinv0 _ _ @ _).
      refine (maponpaths (λ z, !z) IHh @ _).
      refine (pathscomp_inv _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp_inv.
      }
      refine (!(path_assoc _ _ _) @ _).
      do 2 apply maponpaths.
      apply pathsinv0inv0.
    - (* transitivity *)
      simpl.
      refine (maponpathscomp0 _ _ _ @ _).
      refine (maponpaths (λ z, z @ _) IHh₁ @ _).
      refine (maponpaths (λ z, _ @ z) IHh₂ @ _).
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
      apply maponpaths.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply pathsinv0r.
      }
      apply idpath.
    - (* ap on endpoints *)
      simpl.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply pathscomp_inv.
        }
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        do 2 refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            exact (!(maponpathsinv0 _ _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        etrans.
        {
          exact (!(maponpathscomp0 _ _ _)).
        }
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        exact (!IHh).
      }
      clear IHh.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathscomp.
        }
        apply (homotsec_natural' (pr1_endpoint e₃)).
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply pathsinv0l.
      }
      refine (!_).
      apply maponpathscomp.
    - (* associativity *)
      simpl.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply pathscomp_inv.
        }
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpathscomp0.
          }
          apply maponpaths_2.
          apply maponpathscomp.
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply pathsinv0l.
      }
      simpl.
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply pathscomp_inv.
        }
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        apply pathsinv0l.
      }
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp0rid.
      }
      apply pathsinv0l.
    - (* left identity *)
      exact (!pathsinv0l _).
    - (* right identity *)
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (pathscomp0rid _ @ _).
        apply maponpathsidfun.
      }
      apply pathsinv0l.
    - (* first projection *)
      simpl.
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply pathscomp0rid.
        }
        apply maponpaths_pr1_pathsdirprod.
      }
      apply pathsinv0l.
    - (* first projection *)
      simpl.
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply pathscomp0rid.
        }
        apply maponpaths_pr2_pathsdirprod.
      }
      apply pathsinv0l.
    - (* pair of endpoints *)
      simpl.
      etrans.
      {
        refine (!_).
        apply maponpaths_pathsdirprod.
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_concat.
        }
        etrans.
        {
          apply maponpaths_2.
          apply pathsdirprod_inv.
        }
        apply pathsdirprod_concat.
      }
      refine (!_).
      exact (paths_pathsdirprod IHh₁ IHh₂).
    - (* composition with pair *)
      simpl.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths_prod_path.
            }
            apply pathsdirprod_concat.
          }
          apply pathsdirprod_inv.
        }
        apply pathsdirprod_concat.
      }
      exact (paths_pathsdirprod (pathsinv0l _) (pathsinv0l _)).
    - (* composition with constant *)
      simpl.
      refine (!_).
      etrans.
      {
        apply pathscomp0rid.
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply pathscomp0rid.
        }
        apply maponpaths_for_constant_function.
      }
      apply idpath.
    - (* path constructor *)
      simpl.
      etrans.
      {
        exact (maponpaths_pr1_PathOverToTotalPath'
                 _
                 (composePathOver
                    (inversePathOver (pr2_endpoint (path_left Σ j) _))
                    (composePathOver
                       (disp_alg_path
                          Y j
                          (poly_pr1 (path_source Σ j) _)
                          _)
                       (pr2_endpoint (path_right Σ j) _)))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp_inv.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      refine (!_).
      refine (homotsec_natural
               (alg_path X j)
               (pr1_endpoint e x)
               @ _).
      apply maponpaths_2.
      apply maponpathsinv0.
    - (* path argument *)
      simpl.
      refine (!_).
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          apply pathsinv0l.
        }
        simpl.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
  Qed.

  Local Definition PathOver_poly_pr2_operation
        {x₁ x₂ : poly_act (point_constr Σ) carrier}
        (q : x₁ = x₂)
    : globe_over
        Y
        (maponpathscomp operation pr1 _
         @ !(maponpathscomp (poly_pr1 _) (alg_constr X) _))
        (PathOver_poly_pr2 I (maponpaths operation q))
        (@apd_2
           _ _
           (poly_dact (point_constr Σ) (pr1 Y))
           (poly_dact I (pr1 Y))
           (alg_constr X)
           (disp_alg_constr Y)
           _ _ _ _ _
           (PathOver_poly_pr2 (point_constr Σ) q)).
  Proof.
    induction q.
    unfold globe_over.
    cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply PathOver_poly_pr2_is_idpath.
    }
    apply idpath.
  Qed.

  Local Definition PathOver_poly_pr2_endpoint_path
        {P Q : poly_code}
        (e : endpoint (point_constr Σ) P Q)
        {x₁ x₂ : poly_act P carrier}
        (p : x₁ = x₂)
    : !(pr1_endpoint e x₁)
      @ maponpaths (sem_endpoint_one_types e (pr11 X)) (maponpaths (poly_pr1 P) p)
      @ pr1_endpoint e x₂
      =
      maponpaths (poly_pr1 Q) (maponpaths (sem_endpoint_UU e operation) p).
  Proof.
    induction p.
    apply pathsinv0l.
  Qed.

  Local Definition PathOver_poly_pr2_endpoint
        {P Q : poly_code}
        (e : endpoint (point_constr Σ) P Q)
        {x₁ x₂ : poly_act P carrier}
        (p : x₁ = x₂)
    : globe_over
        (poly_dact Q (pr1 Y))
        (PathOver_poly_pr2_endpoint_path e p)
        (composePathOver
           (inversePathOver (pr2_endpoint e x₁))
           (composePathOver
              (@apd_2
                 _ _
                 (poly_dact P (pr1 Y))
                 (poly_dact Q (pr1 Y))
                 _
                 (@endpoint_dact _ _ (pr1 Y) _ _ e (disp_alg_constr Y))
                 _ _
                 (maponpaths (poly_pr1 P) p)
                 _ _
                 (PathOver_poly_pr2 P p))
              (pr2_endpoint e x₂)))
        (PathOver_poly_pr2
           Q
           (maponpaths (sem_endpoint_UU e operation) p)).
  Proof.
    induction p.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | Z₁ Z₂ f | ].
    - (* identity *)
      apply TODO.
    - (* composition *)
      apply TODO.
    - (* inl *)
      apply TODO.
    - (* inr *)
      apply TODO.
    - (* pr1 *)
      apply TODO.
    - (* pr2 *)
      apply TODO.
    - (* pair *)
      apply TODO.
    - (* constant *)
      apply TODO.
    - (* constant function *)
      apply TODO.
    - (* constructor *)
      simpl.
      pose (PathOver_poly_pr2_operation (idpath x₁)).
      simpl in g.
      apply TODO.
  Qed.

  Local Definition pr2_homot_endpoint
        {Q : poly_code}
        {TR : poly_code}
        {al ar : endpoint (point_constr Σ) Q TR}
        {T : poly_code}
        {sl sr : endpoint (point_constr Σ) Q T}
        (h : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
        (x : poly_act
               Q
               (∑ x, pr1 Y x))
        (p : sem_endpoint_UU al operation x
             =
             sem_endpoint_UU ar operation x)
    : globe_over
        (poly_dact T (pr1 Y))
        (pr1_homot_endpoint h x p)
        (PathOver_poly_pr2
           _
           (sem_homot_endpoint_UU
              h
              (∑ x0 : path_alg_carrier (pr1 X), pr1 Y x0)
              operation paths x p))
        (composePathOver
           (inversePathOver (pr2_endpoint _ _))
           (composePathOver
              (homot_endpoint_dact
                 h
                 (disp_alg_constr Y)
                 (disp_alg_path Y)
                 _
                 (composePathOver
                    (pr2_endpoint _ _)
                    (composePathOver
                       (PathOver_poly_pr2 _ p)
                       (inversePathOver (pr2_endpoint _ _)))))
              (pr2_endpoint _ _))).
  Proof.
    induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ e₃
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | P R e₁ e₂ | P R e₁ e₂
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | P₁ P₂ P₃ e₁ e₂ e₃
                    | W w T e
                    | j e | ].
    - (* identity *)
      use globe_over_move_globe_one_type.
      { apply poly_act_hlevel. }
      { exact (!(pathsinv0l _)). }
      use inv_globe_over.
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      simple refine 
      (concat_globe_over
         (globe_over_compose_left'
            (inversePathOver (pr2_endpoint e x))
            (globe_over_id_left (pr2_endpoint e x)))
         (concat_globe_over
            (globe_over_inv_left _)
            _)).
      { apply idpath. }
      exact (!(PathOver_poly_pr2_is_idpath _ _)).
    - (* symmetry *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (concat_globe_over
         (PathOver_pr1_PathOver_poly_inv _)
         (concat_globe_over
            (globe_over_on_inv IHh)
            (concat_globe_over
               (globe_over_comp_inv _ _)
               (concat_globe_over
                  (globe_over_compose_left'
                     _
                     (globe_over_inv_inv _))
                  (concat_globe_over
                     (globe_over_compose_right
                        (pr2_endpoint e₁ x)
                        (globe_over_comp_inv _ _)
                     )
                     (globe_over_assocr _ _ _)))))).
    - (* transitivity *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (concat_globe_over
         (PathOver_pr1_PathOver_poly_concat _ _)
         (concat_globe_over
            (globe_over_compose_right _ IHh₁)
            (concat_globe_over
               (globe_over_compose_left' _ IHh₂)
               (concat_globe_over
                  (globe_over_assocr _ _ _)
                  (globe_over_compose_left'
                     _
                     (concat_globe_over
                        (globe_over_assocl _ _ _)
                        (concat_globe_over
                           (globe_over_assocl _ _ _)
                           (globe_over_compose_right
                              _
                              (globe_over_compose_right
                                 _
                                 (concat_globe_over
                                    (globe_over_assocr _ _ _)
                                    (concat_globe_over
                                       (globe_over_compose_left'
                                          _
                                          (globe_over_inv_right _))
                                       (globe_over_id_right _)))))))))))).
    - (* ap endpoint *)
      simpl.
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (inv_globe_over
         (concat_globe_over
            (globe_over_compose_left'
               _
               (concat_globe_over
                  (globe_over_assocl _ _ _)
                  (globe_over_compose_right
                     _
                     (inv_globe_over
                        (apd2_concat _ _ _)))))
            (concat_globe_over
               (globe_over_compose_right
                  _
                  (globe_over_comp_inv _ _))
               (concat_globe_over
                  (concat_globe_over
                     (globe_over_assocr _ _ _)
                     (globe_over_compose_left'
                        _
                        (concat_globe_over
                           (globe_over_assocl _ _ _)
                           (globe_over_compose_right
                              _
                              (concat_globe_over
                                 (globe_over_compose_right
                                    _
                                    (apd2_inv _ _))
                                 (inv_globe_over
                                    (apd2_concat _ _ _)))))))
                  (concat_globe_over
                     (globe_over_compose_left'
                        _
                        (globe_over_compose_right
                           _
                           (apd2_globe_over
                              _
                              (inv_globe_over IHh))))
                     (PathOver_poly_pr2_endpoint e₃ _)))))).
    - (* associativity *)
      simpl.
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (concat_globe_over
         (PathOver_poly_pr2_is_idpath_globe _ _)
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (concat_globe_over
                     (globe_over_id_left _)
                     (globe_over_compose_right
                        _
                        (concat_globe_over
                           (apd2_concat _ _ _)
                           (globe_over_compose_right
                              _
                              (apd2_comp _ _ _))))))
               (concat_globe_over
                  (globe_over_compose_left'
                     _
                     (globe_over_assocr _ _ _))
                  (globe_over_inv_left _))))).
    - (* left identity *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (concat_globe_over
         (PathOver_poly_pr2_is_idpath_globe _ _)
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (globe_over_id_left _))
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (globe_over_on_inv
                        (globe_over_id_left _)))
                  (globe_over_inv_left _))))).
    - (* right identity *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (concat_globe_over
         (PathOver_poly_pr2_is_idpath_globe _ _)
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (globe_over_id_left _))
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (globe_over_on_inv
                        (concat_globe_over
                           (globe_over_id_right _)
                           (apd2_idfun _))))
                  (globe_over_inv_left _))))).
    - (* first projection *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (concat_globe_over
         (PathOver_pr1_PathOver_poly_pr2 (idpath _))
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (globe_over_id_left _))
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (globe_over_on_inv
                        (concat_globe_over
                           (globe_over_id_right _)
                           (PathOver_pr1_pair _ _))))
                  (globe_over_inv_left _))))).
    - (* second projection *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (concat_globe_over
         (PathOver_pr2_PathOver_poly_pr2 (idpath _))
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (globe_over_id_left _))
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (globe_over_on_inv
                        (concat_globe_over
                           (globe_over_id_right _)
                           (PathOver_pr2_pair _ _))))
                  (globe_over_inv_left _))))).
    - (* pair of endpoints *)
      refine (globe_over_move_globe_one_type _ _).
      { apply (poly_act_hlevel (T₁ * T₂)). }
      exact
      (concat_globe_over
         (PathOver_pr2_PathOver_pair _ _)
         (concat_globe_over
            (globe_over_PathOver_pair IHh₁ IHh₂)
            (concat_globe_over
               (PathOver_pair_concat _ _ _ _)
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (PathOver_pair_inv _ _))
                  (globe_over_compose_left'
                     _
                     (PathOver_pair_concat _ _ _ _)))))).
    - (* composition of pair *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (inv_globe_over
         (concat_globe_over
            (globe_over_compose_left'
               _
               (globe_over_id_left _))
            (concat_globe_over
               (globe_over_compose_right
                  _
                  (globe_over_on_inv
                     (concat_globe_over
                        (globe_over_compose_right
                           _
                           (apd2_dep_pair_fun _ _ _))
                        (inv_globe_over
                           (PathOver_pair_concat _ _ _ _)))))
               (globe_over_inv_left _)))).
    - (* composition of constant *)
      refine (globe_over_move_globe_one_type _ _).
      { apply one_type_isofhlevel. }
      simpl.
      refine
      (inv_globe_over
         (concat_globe_over
            (globe_over_compose_left'
               _
               (globe_over_id_left _))
            (concat_globe_over
               (globe_over_id_right _)
               (concat_globe_over
                  (globe_over_on_inv
                     (concat_globe_over
                        (globe_over_id_right _)
                        _))
                  _)))).
      + exact (apd_2_dep_const_fun _ _ _ _).
      + apply globe_over_identity.
    - (* path constructor *)
      simpl.
      refine (globe_over_move_globe_one_type _ _).
      { apply one_type_isofhlevel. }
      refine
      (concat_globe_over
         (TotalPathToPathOver_PathOverToTotalPath' _ _)
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_right
                  _
                  (globe_over_comp_inv _ _))
               (concat_globe_over
                  (globe_over_assocr _ _ _)
                  (globe_over_compose_left'
                     _
                     (concat_globe_over
                        (globe_over_assocl _ _ _)
                        (concat_globe_over
                           (globe_over_assocl _ _ _)
                           (globe_over_compose_right
                              _
                              (PathOver_natural
                                 _
                                 (disp_alg_path Y j)
                                 (pr2_endpoint e x)))))))))).
      apply one_type_isofhlevel.
      (*
    - (* point constructor *)
      refine (globe_over_move_globe_one_type _ _).
      { apply one_type_isofhlevel. }
      simple refine
      (concat_globe_over
         (PathOver_poly_pr2_operation _)
         (concat_globe_over
            (apd2_globe_over _ IHh)
            (concat_globe_over
               (apd2_concat _ _ _)
               (concat_globe_over
                  (globe_over_compose_left'
                     _
                     (apd2_concat _ _ _))
                  (inv_globe_over
                     (concat_globe_over
                        (globe_over_compose_left'
                           _
                           (globe_over_compose_left'
                              _
                              (globe_over_id_right _)))
                        (globe_over_compose_right
                           _
                           (concat_globe_over
                              (globe_over_on_inv
                                 (globe_over_id_right  _))
                              (apd2_inv _ _))))))))).
       *)
    - (* path argument *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      exact
      (inv_globe_over
         (concat_globe_over
            (globe_over_compose_left'
               _
               (concat_globe_over
                  (globe_over_assocr _ _ _)
                  (globe_over_compose_left'
                     _
                     (concat_globe_over
                        (globe_over_assocr _ _ _)
                        (concat_globe_over
                           (globe_over_compose_left'
                              _
                              (globe_over_inv_left _))
                           (globe_over_id_right _))))))
            (concat_globe_over
               (globe_over_assocl _ _ _)
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (globe_over_inv_left _))
                  (globe_over_id_left _))))).
  Qed.
  
  Local Definition homots
        (j : homot_label Σ)
        (x : poly_act
               (homot_point_arg Σ j)
               (∑ x, pr1 Y x))
        (p : sem_endpoint_UU (homot_path_arg_left Σ j) operation x
             =
             sem_endpoint_UU (homot_path_arg_right Σ j) operation x)
    : sem_homot_endpoint_one_types
        (homot_left_path Σ j)
        total_prealgebra paths
        x p
      =
      sem_homot_endpoint_one_types
        (homot_right_path Σ j)
        total_prealgebra paths
        x p.
  Proof.
    unfold sem_homot_endpoint_one_types.
    cbn.
    refine (path_is_PathOverToTotalPath' _ @ _).
    refine (_ @ !(path_is_PathOverToTotalPath' _)).
    use globe_over_to_homot.
    - refine (pr1_homot_endpoint (homot_left_path Σ j) _ _
              @ _
              @ !(pr1_homot_endpoint (homot_right_path Σ j) _ _)).
      refine (maponpaths (λ z, _ @ (z @ _)) _).
      exact (alg_homot
               X j
               (poly_pr1 _ x)
               ((pr1_endpoint _ x)
                @ maponpaths (poly_pr1 _) p
                @ !(pr1_endpoint _ x))).
    - simpl.
      simple refine
             (concat_globe_over
                (pr2_homot_endpoint
                   (homot_left_path Σ j)
                   x p)
                (concat_globe_over
                   _
                   (inv_globe_over
                      (pr2_homot_endpoint
                         (homot_right_path Σ j)
                         x p)))).
      use globe_over_compose_left.
      use globe_over_compose_right.
      apply (disp_alg_homot
               Y j
               (poly_pr1 _ x)
               (poly_pr2 _ x)
               ((pr1_endpoint _ x)
                @ maponpaths
                    (poly_pr1 (homot_path_arg_target Σ j))
                    p
                @ !(pr1_endpoint _ x))
               _).
  Qed.
    
  Definition total_algebra
    : hit_algebra_one_types Σ.
  Proof.
    use make_algebra.
    - use make_hit_path_algebra.
      + exact total_prealgebra.
      + exact paths.
    - exact homots.
  Defined.
End TotalAlgebra.

(**
We can project the total algebra on `X`.
 *)
Section Projection.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}.
  Variable (Y : disp_algebra X).

  Definition projection_help
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (carrier Y))
    : pr1_endpoint Y e _
      @ @sem_endpoint_UU_natural
          (point_constr Σ)
          P Q e
          (∑ x0 : path_alg_carrier (pr1 X), pr1 Y x0) _ (operation Y) 
          (pr211 X)
          pr1
          (λ _, idpath _)
          x
      =
      idpath _.
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | Z₁ Z₂ f | ]
    ; try (apply idpath).
    - simpl.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply IHe₂.
      }
      simpl.
      etrans.
      {
        refine (!_).
        apply maponpathscomp0.
      }
      etrans.
      {
        apply maponpaths.
        apply IHe₁.
      }
      apply idpath.
    - simpl.
      etrans.
      {
        apply pathsdirprod_concat.
      }
      exact (paths_pathsdirprod (IHe₁ x) (IHe₂ x)).
  Defined.

  Definition projection
    : total_algebra Y --> X.
  Proof.
    use make_algebra_map.
    - use make_hit_path_alg_map.
      + use tpair.
        * exact pr1.
        * use make_invertible_2cell.
          ** intro.
             apply idpath.
          ** apply one_type_2cell_iso.
      + intros i x.
        simpl.
        etrans.
        {
          apply maponpaths_2.
          unfold paths.
          exact (maponpaths_pr1_PathOverToTotalPath
                   _
                   (composePathOver
                      (inversePathOver (pr2_endpoint Y (path_left Σ i) x))
                      (composePathOver
                         (disp_alg_path
                            Y i (poly_pr1 (path_source Σ i) x)
                            (poly_pr2 (path_source Σ i) x))
                         (pr2_endpoint Y (path_right Σ i) x)))).
        }
        etrans.
        {
          refine (!(path_assoc _ _ _) @ _).
          apply maponpaths.
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply (projection_help (path_right Σ i)).
          }
          apply pathscomp0rid.
        }
        apply maponpaths_2.
        apply pathsinv0_to_right'.
        refine (!_).
        apply (projection_help (path_left Σ i)).
  Defined.
End Projection.
