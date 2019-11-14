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

Local Open Scope cat.

Definition inv_globe_over
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p q : x₁ = x₂}
           {g : globe p q}
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp : PathOver y₁ y₂ p}
           {qq : PathOver y₁ y₂ q}
           (gg : globe_over Y g pp qq)
  : globe_over Y (! g) qq pp.
Proof.
  induction g ; simpl.
  exact (!gg).
Qed.

Definition concat_globe_over
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p q r : x₁ = x₂}
           {g₁ : globe p q}
           {g₂ : globe q r}
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp : PathOver y₁ y₂ p}
           {qq : PathOver y₁ y₂ q}
           {rr : PathOver y₁ y₂ r}
           (gg₁ : globe_over Y g₁ pp qq)
           (gg₂ : globe_over Y g₂ qq rr) 
  : globe_over Y (g₁ @ g₂) pp rr.
Proof.
  induction g₁, g₂.
  exact (gg₁ @ gg₂).
Qed.

Definition globe_over_compose_left
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ x₃ x₄ : X}
           {p : x₁ = x₂} {q₁ q₂ : x₂ = x₃} {r : x₃ = x₄}
           {y₁ : Y x₁} {y₂ : Y x₂} {y₄ : Y x₄}
           (pp : PathOver y₁ y₂ p)
           (qq₁ : PathOver y₂ y₄ (q₁ @ r))
           (qq₂ : PathOver y₂ y₄ (q₂ @ r))
           (g : globe q₁ q₂)
           (gg : globe_over Y (maponpaths (λ z, z @ r) g) qq₁ qq₂)
  : globe_over
      Y
      (maponpaths (λ (h : x₂ = x₃), p @ (h @ r)) g)
      (composePathOver pp qq₁)
      (composePathOver pp qq₂).
Proof.
  induction g, p, q₁, r.
  exact (maponpaths (λ z, pp @ z) gg).
Qed.

Definition globe_over_compose_right
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ x₃ : X}
           {p₁ p₂ : x₁ = x₂} {q : x₂ = x₃} 
           {y₁ : Y x₁} {y₂ : Y x₂} {y₃ : Y x₃}
           (pp₁ : PathOver y₁ y₂ p₁)
           (pp₂ : PathOver y₁ y₂ p₂)
           (qq : PathOver y₂ y₃ q)
           (g : globe p₁ p₂)
           (gg : globe_over Y g pp₁ pp₂)
  : globe_over
      Y
      (maponpaths (λ h, h @ q) g)
      (composePathOver pp₁ qq)
      (composePathOver pp₂ qq).
Proof.
  induction g, p₁, q.
  exact (maponpaths (λ z, z @ _) gg).
Qed.

Definition globe_over_id_left
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathscomp0lid _)
      (composePathOver
         (identityPathOver _)
         pp)
      pp.
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_id_right
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathscomp0rid _)
      (composePathOver
         pp
         (identityPathOver _))
      pp.
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_inv_left
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathsinv0l _)
      (composePathOver
         (inversePathOver pp)
         pp)
      (identityPathOver _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_inv_right
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathsinv0r _)
      (composePathOver
         pp
         (inversePathOver pp))
      (identityPathOver _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_move_globe
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p₁ p₂ : x₁ = x₂} 
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp₁ : PathOver y₁ y₂ p₁}
           {pp₂ : PathOver y₁ y₂ p₂}
           {g₁ g₂ : globe p₁ p₂}
           (h : g₁ = g₂)
           (gg : globe_over Y g₁ pp₁ pp₂)
  : globe_over Y g₂ pp₁ pp₂.
Proof.
  induction h.
  exact gg.
Qed.

Definition globe_over_move_globe_one_type
           {X : UU}
           (HX : isofhlevel 3 X)
           {Y : X → UU}
           {x₁ x₂ : X}
           {p₁ p₂ : x₁ = x₂} 
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp₁ : PathOver y₁ y₂ p₁}
           {pp₂ : PathOver y₁ y₂ p₂}
           {g₂ : globe p₁ p₂}
           (gg : ∑ g₁, globe_over Y g₁ pp₁ pp₂)
  : globe_over Y g₂ pp₁ pp₂.
Proof.
  use globe_over_move_globe.
  - exact (pr1 gg).
  - exact (pr1 (HX x₁ x₂ p₁ p₂ (pr1 gg) g₂)).
  - exact (pr2 gg).    
Qed.


Definition TotalPathToPathOver
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : x = y)
  : PathOver (pr2 x) (pr2 y) (maponpaths pr1 p).
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Definition PathOverToTotalPath'
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : pr1 x = pr1 y)
           (q : PathOver (pr2 x) (pr2 y) p)
  : x = y.
Proof.
  use PathOverToTotalPath.
  - exact p.
  - exact q.
Defined.

Definition globe_over_to_homot
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           {p₁ p₂ : pr1 x = pr1 y}
           (q₁ : PathOver (pr2 x) (pr2 y) p₁)
           (q₂ : PathOver (pr2 x) (pr2 y) p₂)
           (g : globe p₁ p₂)
           (gg : globe_over Y g q₁ q₂)
  : PathOverToTotalPath' _ q₁ = PathOverToTotalPath' _ q₂.
Proof.
  induction g ; simpl in *.
  unfold globe_over in gg.
  cbn in gg.
  unfold idfun in gg.
  apply maponpaths.
  refine (_ @ maponpaths path_to_PathOver gg @ _).
  - exact (!(homotinvweqweq (make_weq _ (PathOver_to_path_isweq _ _ _)) q₁)).
  - exact (homotinvweqweq (make_weq _ (PathOver_to_path_isweq _ _ _)) q₂).
Defined.

Definition path_is_PathOverToTotalPath'
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : x = y)
  : p
    =
    PathOverToTotalPath'
      _
      (TotalPathToPathOver p).
Proof.
  induction p.
  apply idpath.
Defined.
  
Definition maponpaths_pr1_PathOverToTotalPath
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ : Y x₁} {y₂ : Y x₂}
           (q : PathOver y₁ y₂ p)
  : maponpaths pr1 (PathOverToTotalPath q)
    =
    p.
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.

Definition maponpaths_pr1_PathOverToTotalPath'
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : pr1 x = pr1 y)
           (q : PathOver (pr2 x) (pr2 y) p)
  : maponpaths pr1 (PathOverToTotalPath' p q)
    =
    p.
Proof.
  induction x as [x₁ x₂], y as [y₁ y₂].
  simpl in *.
  induction p.
  induction q.
  apply idpath.
Qed.

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

Definition TODO {A : UU} : A.
Admitted.

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
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | T₁ T₂ e₁ e₂ e₃ e₄ h IHh | T₁ T₂ e₁ e₂ e₃ e₄ h IHh
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                    | j e | el er | ].
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
      simpl ; simpl in IHh.
      refine (_ @ maponpaths (maponpaths pr1) IHh @ _).
      + refine (_ @ !(maponpathscomp (dirprodf (poly_pr1 T₁) (poly_pr1 T₂)) pr1 _)).
        exact (maponpathscomp
                 pr1
                 (poly_pr1 T₁)
                 (sem_homot_endpoint_UU
                    h
                    (∑ z, pr1 Y z)
                    operation paths
                    x p)).
      + etrans.
        {
          etrans.
          {
            apply maponpathscomp0.
          }
          apply maponpaths.
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply maponpaths_pr1_pathsdirprod.
        }
        do 2 apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
    - (* second projection *)
      simpl ; simpl in IHh.
      refine (_ @ maponpaths (maponpaths dirprod_pr2) IHh @ _).
      + refine (_ @ !(maponpathscomp (dirprodf (poly_pr1 T₁) (poly_pr1 T₂)) pr2 _)).
        exact (maponpathscomp
                 dirprod_pr2
                 (poly_pr1 T₂)
                 (sem_homot_endpoint_UU
                    h
                    (∑ z, pr1 Y z)
                    operation paths
                    x p)).
      + etrans.
        {
          etrans.
          {
            apply maponpathscomp0.
          }
          apply maponpaths.
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply maponpaths_pr2_pathsdirprod.
        }
        do 2 apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
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
    - (* left inclusion *)
      simpl.
      refine (coprodf_path_maponpaths_inl _ _ _ @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathsinv0.
        }
        refine (!_).
        apply (maponpathscomp0 inl).
      }
      apply maponpaths.
      exact (!IHh).
    - (* right inclusion *)
      simpl.
      refine (coprodf_path_maponpaths_inr _ _ _ @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathsinv0.
        }
        refine (!_).
        apply (maponpathscomp0 inr).
      }
      apply maponpaths.
      exact (!IHh).
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
    - (* point constructor *)
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
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathsinv0.
        }
        etrans.
        {
          do 2 apply maponpaths.
          apply pathscomp0rid.
        }
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
        apply (maponpathscomp operation pr1).
      }
      etrans.
      {
        exact (!(maponpathscomp (poly_pr1 _) (alg_constr X) _)).
      }
      exact (maponpaths (maponpaths (alg_constr X)) IHh).
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
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | T₁ T₂ e₁ e₂ e₃ e₄ h IHh | T₁ T₂ e₁ e₂ e₃ e₄ h IHh
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                    | j e | el er | ].
    - (* identity *)
      (*
      Opaque composePathOver.
      simpl.
      rewrite PathOver_poly_pr2_is_idpath.
      use globe_over_move_globe_one_type.
      { apply poly_act_hlevel. }
      refine (_ ,, _).
      refine (inv_globe_over _).
      refine (concat_globe_over
                (globe_over_compose_left
                   (inversePathOver (pr2_endpoint e x))
                   (composePathOver
                      (identityPathOver _)
                      (pr2_endpoint e x))
                   _
                   _
                   _)                     
                _).
        * use globe_over_move_globe_one_type.
          { apply poly_act_hlevel. }
          refine (_ ,, _).
          apply globe_over_id_right.
                     (composePathOver
                        (identityPathOver _)
                     (pr2_endpoint e x))
                  (pr2_endpoint e x)
                  (inversePathOver (pr2_endpoint e x))
                  _
                  (globe_over_id_left _))
                  _).
      refine (globe_over_move_globe
               _
               (concat_globe_over
               (globe_over_compose_right
                  (composePathOver
                     (identityPathOver _)
                     (pr2_endpoint e x))
                  (pr2_endpoint e x)
                  (inversePathOver (pr2_endpoint e x))
                  _
                  (globe_over_id_left _))
               (globe_over_inv_right _))).
      
      refine (globe_over_move_globe
                _
                (concat_globe_over
                   (globe_over_compose_right
                      (composePathOver
                         (identityPathOver _)
                         (pr2_endpoint e x))
                      (pr2_endpoint e x)
                      (inversePathOver (pr2_endpoint e x))
                      _
                      _)
                   _)).
      Opaque composePathOver.
      simpl.
       *)
      apply TODO.
    - (* symmetry *)
      apply TODO.
    - (* transitivity *)
      apply TODO.
    - (* associativity *)
      apply TODO.
    - (* left identity *)
      apply TODO.
    - (* right identity *)
      apply TODO.
    - (* first projection *)
      apply TODO.
    - (* second projection *)
      apply TODO.
    - (* pair of endpoints *)
      apply TODO.
    - (* left inclusion *)
      apply TODO.
    - (* right inclusion *)
      apply TODO.
    - (* path constructor *)
      apply TODO.
    - (* point constructor *)
      apply TODO.
    - (* path argument *)
      apply TODO.
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
