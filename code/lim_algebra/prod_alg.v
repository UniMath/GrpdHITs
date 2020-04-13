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
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.globe_over_lem.
Require Import displayed_algebras.constant_display.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

Definition alg_map_carrier
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           (f : X --> Y)
  : alg_carrier X → alg_carrier Y
  := pr111 f.

Definition alg_map_commute
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           (f : X --> Y)
  : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
    alg_map_carrier f (alg_constr X x)
    =
    alg_constr Y (poly_map (point_constr Σ) (alg_map_carrier f) x)
  := pr1 (pr211 f).

Definition is_algebra_2cell
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           {f g : X --> Y}
           (α : alg_map_carrier f ~ alg_map_carrier g)
  : UU
  := ∏ (z : poly_act (point_constr Σ) (alg_carrier X)),
     α (alg_constr X z)
     @ alg_map_commute g z
     =
     alg_map_commute f z
     @ maponpaths (alg_constr Y) (poly_homot (point_constr Σ) α z).
           
Definition make_algebra_2cell
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           {f g : X --> Y}
           (α : alg_map_carrier f ~ alg_map_carrier g)
           (Hα : is_algebra_2cell α)
  : f ==> g.
Proof.
  simple refine (((α ,, _) ,, λ _, tt) ,, tt).
  use funextsec.
  exact Hα.
Defined.

Definition poly_homot_pathsdirprod_pr1
           {P : poly_code}
           {X Y₁ Y₂ : UU}
           {f₁ f₂ : X → Y₁} {g₁ g₂ : X → Y₂}
           {p : f₁ ~ f₂} {q : g₁ ~ g₂}
           (x : poly_act P X)
  : maponpaths
      (poly_map P pr1)
      (poly_homot
         P
         (λ z,
          pathsdirprod
            (p z)
            (q z))
         x)
    =
    poly_comp _ _ _ _
    @ poly_homot P p x
    @ !(poly_comp _ _ _ _).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - exact (maponpaths_pr1_pathsdirprod _ _ @ !(pathscomp0rid _)).
  - induction x as [x | x] ; simpl.
    + etrans.
      {
        apply (maponpathscomp inl (coprodf _ _)).
      }
      unfold funcomp ; cbn.
      etrans.
      {
        etrans.
        {
          refine (!_).
          apply maponpathscomp.
        }
        apply maponpaths.
        apply IHP₁.
      }
      etrans.
      {
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        apply maponpathscomp0.
      }
      do 2 apply maponpaths.
      apply maponpathsinv0.
    + etrans.
      {
        apply (maponpathscomp inr (coprodf _ _)).
      }
      unfold funcomp ; cbn.
      etrans.
      {
        etrans.
        {
          refine (!_).
          apply maponpathscomp.
        }
        apply maponpaths.
        apply IHP₂.
      }
      etrans.
      {
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        apply maponpathscomp0.
      }
      do 2 apply maponpaths.
      apply maponpathsinv0.
  - simpl.
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
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_inv.
        }
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    refine (!_).
    exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition poly_homot_pathsdirprod_pr2
           {P : poly_code}
           {X Y₁ Y₂ : UU}
           {f₁ f₂ : X → Y₁} {g₁ g₂ : X → Y₂}
           {p : f₁ ~ f₂} {q : g₁ ~ g₂}
           (x : poly_act P X)
  : maponpaths
      (poly_map P dirprod_pr2)
      (poly_homot
         P
         (λ z,
          pathsdirprod
            (p z)
            (q z))
         x)
    =
    poly_comp _ _ _ _
    @ poly_homot P q x
    @ !(poly_comp _ _ _ _).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - exact (maponpaths_pr2_pathsdirprod _ _ @ !(pathscomp0rid _)).
  - induction x as [x | x] ; simpl.
    + etrans.
      {
        apply (maponpathscomp inl (coprodf _ _)).
      }
      unfold funcomp ; cbn.
      etrans.
      {
        etrans.
        {
          refine (!_).
          apply maponpathscomp.
        }
        apply maponpaths.
        apply IHP₁.
      }
      etrans.
      {
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        apply maponpathscomp0.
      }
      do 2 apply maponpaths.
      apply maponpathsinv0.
    + etrans.
      {
        apply (maponpathscomp inr (coprodf _ _)).
      }
      unfold funcomp ; cbn.
      etrans.
      {
        etrans.
        {
          refine (!_).
          apply maponpathscomp.
        }
        apply maponpaths.
        apply IHP₂.
      }
      etrans.
      {
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        apply maponpathscomp0.
      }
      do 2 apply maponpaths.
      apply maponpathsinv0.
  - simpl.
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
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_inv.
        }
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    refine (!_).
    exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition poly_homot_inv
           {P : poly_code}
           {X Y : one_type}
           {f g : X → Y}
           (p : f ~ g)
           (x : poly_act P X)
  : poly_homot P (invhomot p) x
    =
    !(poly_homot P p x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + simpl.
      refine (maponpaths (maponpaths inl) (IHP₁ x) @ _).
      apply maponpathsinv0.
    + simpl.
      refine (maponpaths (maponpaths inr) (IHP₂ x) @ _).
      apply maponpathsinv0.
  - simpl.
    refine (_ @ !(pathsdirprod_inv _ _)).
    exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition poly_pr1_poly_map
           {P : poly_code}
           {X Y Z : one_type}
           (f : X → Y)
           (g : X → Z)
           (x : poly_act P X)
  : poly_map P f x
    =
    poly_pr1
      P
      (poly_map
         P
         (λ z, f z ,, g z)
         x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths inl (IHP₁ x)).
    + exact (maponpaths inr (IHP₂ x)).
  - exact (pathsdirprod
             (IHP₁ (pr1 x))
             (IHP₂ (pr2 x))).
Defined.

Section ProductAlg.
  Context {Σ : hit_signature}
          (X Y : hit_algebra_one_types Σ).

  Local Notation "'P'" := (alg_carrier X × alg_carrier Y).

  Local Definition prod_point_constr
    : poly_act (point_constr Σ) P → P
    := λ x,
       alg_constr X (poly_map (point_constr Σ) (λ (z : P), pr1 z) x)
       ,,
       alg_constr Y (poly_map (point_constr Σ) (λ (z : P), pr2 z) x).

  Definition prod_prealg
    : hit_prealgebra_one_types Σ.
  Proof.
    use make_hit_prealgebra.
    - exact P.
    - abstract
        (apply isofhleveldirprod
         ; [apply (pr111 X) | apply (pr111 Y)]).
    - exact prod_point_constr.
  Defined.

  Local Definition prod_endpoint_pr1
        {Q R : poly_code}
        (e : endpoint (point_constr Σ) Q R)
        (x : poly_act Q P)
    : sem_endpoint_UU
        e
        (alg_constr X)
        (poly_map Q (λ (z : P), pr1 z) x)
      =
      poly_map
        R
        (λ (z : P), pr1 z)
        (sem_endpoint_UU e prod_point_constr x).
  Proof.
    refine (!(sem_endpoint_UU_natural
                e
                (λ (z : poly_act (point_constr Σ) P), _)
                x)).
    exact (idpath (alg_constr X _)).
  Defined.

  Local Definition prod_endpoint_pr2
        {Q R : poly_code}
        (e : endpoint (point_constr Σ) Q R)
        (x : poly_act Q P)
    : sem_endpoint_UU
        e
        (alg_constr Y)
        (poly_map Q (λ (z : P), pr2 z) x)
      =
      poly_map
        R
        (λ (z : P), pr2 z)
        (sem_endpoint_UU e prod_point_constr x).
  Proof.
    refine (!(sem_endpoint_UU_natural
                e
                (λ (z : poly_act (point_constr Σ) P), _)
                x)).
    exact (idpath _).
  Defined.

  Local Definition prod_path_constr
    :  ∏ (j : path_label Σ)
         (x : poly_act (path_source Σ j) P),
       sem_endpoint_UU (path_left Σ j) prod_point_constr x
       =
       sem_endpoint_UU (path_right Σ j) prod_point_constr x.
  Proof.
    exact (λ j x,
           pathsdirprod
             (!(prod_endpoint_pr1 _ _)
              @ alg_path X j (poly_map _ (λ (z : P), pr1 z) x)
              @ prod_endpoint_pr1 _ _)
             (!(prod_endpoint_pr2 _ _)
              @ alg_path Y j (poly_map _ (λ (z : P), pr2 z) x)
              @ prod_endpoint_pr2 _ _)).
  Defined.
    
  Definition prod_path_alg
    : hit_path_algebra_one_types Σ.
  Proof.
    use make_hit_path_algebra.
    - exact prod_prealg.
    - exact prod_path_constr.
  Defined.

  Definition prod_homot_endpoint_pr1
             {Q TR T : poly_code}
             {al ar : endpoint (point_constr Σ) Q TR}
             {sl sr : endpoint (point_constr Σ) Q T}
             (h : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
             (x : poly_act Q P)
             (p : sem_endpoint_UU al prod_point_constr x
                  =
                  sem_endpoint_UU ar prod_point_constr x)
    : maponpaths
        (poly_map T pr1)
        (sem_homot_endpoint_one_types
           h
           prod_prealg prod_path_constr
           x p)
      =
      !(prod_endpoint_pr1 _ _)
      @ sem_homot_endpoint_one_types
          h
          _ (alg_path X)
          (poly_map Q pr1 x)
          (prod_endpoint_pr1 _ _
           @ maponpaths (poly_map TR pr1) p
           @ !(prod_endpoint_pr1 _ _))
      @ prod_endpoint_pr1 _ _.
  Proof.
    induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ e₃ h IHh
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | R₁ R₂ e₁ e₂ | R₁ R₂ e₁ e₂
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | P₁ P₂ P₃ e₁ e₂ e₃
                    | Z z T e | j e | ].
    - exact (!(pathsinv0l _)).
    - simpl.
      etrans.
      {
        apply maponpathsinv0.
      }
      etrans.
      {
        apply maponpaths.
        exact IHh.
      }
      etrans.
      {
        etrans.
        {
          apply pathscomp_inv.
        }
        etrans.
        {
          apply maponpaths.
          apply pathsinv0inv0.
        }
        apply maponpaths_2.
        apply pathscomp_inv.
      }
      exact (!(path_assoc _ _ _)).
    - simpl.
      etrans.
      {
        apply maponpathscomp0.
      }
      etrans.
      {
        apply maponpaths_2.
        exact IHh₁.
      }
      etrans.
      {
        apply maponpaths.
        exact IHh₂.
      }
      clear IHh₁ IHh₂.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _ @ (path_assoc _ _ _)).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
    - simpl.
      unfold prod_endpoint_pr1 ; simpl.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply pathsinv0inv0.
        }
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
          apply (maponpathsinv0 (sem_endpoint_UU e₃ (alg_constr X))).
        }
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (maponpathscomp0 (sem_endpoint_UU e₃ (alg_constr X))).
        }
        etrans.
        {
          refine (!_).
          apply (maponpathscomp0 (sem_endpoint_UU e₃ (alg_constr X))).
        }
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        refine (_ @ !IHh).
        apply maponpaths_2.
        refine (!_).
        apply pathsinv0inv0.
      }
      etrans.
      {
        apply maponpaths ; apply maponpaths_2.
        apply maponpathscomp.
      }
      refine (path_assoc _ _ _ @ _).
      use path_inv_rotate_lr.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (maponpathscomp (sem_endpoint_UU e₃ prod_point_constr) (poly_map T₂ pr1)).
      }
      apply (homotsec_natural' (sem_endpoint_UU_natural e₃ _)).
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr1 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr1.
      apply maponpaths.
      simpl.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths.
      apply maponpathscomp.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr1 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr1.
      apply maponpaths.
      simpl.
      apply pathscomp0rid.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr1 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr1.
      apply maponpaths.
      apply maponpathsidfun.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr1 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr1.
      apply maponpaths.
      apply maponpaths_pr1_pathsdirprod.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr1 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr1.
      apply maponpaths.
      apply maponpaths_pr2_pathsdirprod.
    - simpl.
      etrans.
      {
        refine (!_).
        apply maponpaths_pathsdirprod.
      }
      refine (paths_pathsdirprod IHh₁ IHh₂ @ _).
      unfold prod_endpoint_pr1.
      rewrite !pathsinv0inv0.
      etrans.
      {
        refine (!_).
        apply pathsdirprod_concat.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply pathsdirprod_concat.
      }
      simpl.
      do 2 apply maponpaths.
      refine (!_).
      apply pathsdirprod_inv.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr1 (comp e₁ (pair e₂ e₃)) x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr1.
      simpl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_prod_path.
      }
      apply pathsdirprod_concat.
    - simpl.
      unfold prod_endpoint_pr1 ; simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply pathsinv0inv0.
        }
        apply maponpaths_for_constant_function.
      }
      apply idpath.
    - simpl.
      unfold prod_path_constr.
      etrans.
      {
        exact (maponpaths_pr1_pathsdirprod _ _).
      }
      unfold prod_endpoint_pr1.
      simpl.
      rewrite !pathsinv0inv0.
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      rewrite pathscomp_inv.
      do 2 refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      refine (_ @ path_assoc _ _ _).
      refine (homotsec_natural (alg_path X j) (prod_endpoint_pr1 _ _) @ _).
      unfold prod_endpoint_pr1.
      rewrite pathsinv0inv0.
      do 2 apply maponpaths.
      apply maponpathsinv0.
    - simpl.
      refine (!_).
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (path_assoc _ _ _ @ _) ; apply maponpaths_2.
        apply pathsinv0l.
      }
      simpl.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
  Qed.

  Definition prod_homot_endpoint_pr2
             {Q TR T : poly_code}
             {al ar : endpoint (point_constr Σ) Q TR}
             {sl sr : endpoint (point_constr Σ) Q T}
             (h : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
             (x : poly_act Q P)
             (p : sem_endpoint_UU al prod_point_constr x
                  =
                  sem_endpoint_UU ar prod_point_constr x)
    : maponpaths
        (poly_map T dirprod_pr2)
        (sem_homot_endpoint_one_types
           h
           prod_prealg prod_path_constr
           x p)
      =
      !(prod_endpoint_pr2 _ _)
      @ sem_homot_endpoint_one_types
          h
          _ (alg_path Y)
          (poly_map Q dirprod_pr2 x)
          (prod_endpoint_pr2 _ _
           @ maponpaths (poly_map TR dirprod_pr2) p
           @ !(prod_endpoint_pr2 _ _))
      @ prod_endpoint_pr2 _ _.
  Proof.
    induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ e₃ h IHh
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | R₁ R₂ e₁ e₂ | R₁ R₂ e₁ e₂
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | P₁ P₂ P₃ e₁ e₂ e₃
                    | Z z T e | j e | ].
    - exact (!(pathsinv0l _)).
    - simpl.
      etrans.
      {
        apply maponpathsinv0.
      }
      etrans.
      {
        apply maponpaths.
        exact IHh.
      }
      etrans.
      {
        etrans.
        {
          apply pathscomp_inv.
        }
        etrans.
        {
          apply maponpaths.
          apply pathsinv0inv0.
        }
        apply maponpaths_2.
        apply pathscomp_inv.
      }
      exact (!(path_assoc _ _ _)).
    - simpl.
      etrans.
      {
        apply maponpathscomp0.
      }
      etrans.
      {
        apply maponpaths_2.
        exact IHh₁.
      }
      etrans.
      {
        apply maponpaths.
        exact IHh₂.
      }
      clear IHh₁ IHh₂.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _ @ (path_assoc _ _ _)).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
    - simpl.
      unfold prod_endpoint_pr1 ; simpl.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply pathsinv0inv0.
        }
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
          apply (maponpathsinv0 (sem_endpoint_UU e₃ (alg_constr Y))).
        }
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (maponpathscomp0 (sem_endpoint_UU e₃ (alg_constr Y))).
        }
        etrans.
        {
          refine (!_).
          apply (maponpathscomp0 (sem_endpoint_UU e₃ (alg_constr Y))).
        }
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        refine (_ @ !IHh).
        apply maponpaths_2.
        refine (!_).
        apply pathsinv0inv0.
      }
      etrans.
      {
        apply maponpaths ; apply maponpaths_2.
        apply maponpathscomp.
      }
      refine (path_assoc _ _ _ @ _).
      use path_inv_rotate_lr.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply (maponpathscomp (sem_endpoint_UU e₃ prod_point_constr) (poly_map T₂ _)).
      }
      apply (homotsec_natural' (sem_endpoint_UU_natural e₃ _)).
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr2 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr2.
      apply maponpaths.
      simpl.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths.
      apply maponpathscomp.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr2 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr2.
      apply maponpaths.
      simpl.
      apply pathscomp0rid.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr2 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr2.
      apply maponpaths.
      apply maponpathsidfun.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr2 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr2.
      apply maponpaths.
      apply maponpaths_pr1_pathsdirprod.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr2 _ x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr2.
      apply maponpaths.
      apply maponpaths_pr2_pathsdirprod.
    - simpl.
      etrans.
      {
        refine (!_).
        apply maponpaths_pathsdirprod.
      }
      refine (paths_pathsdirprod IHh₁ IHh₂ @ _).
      unfold prod_endpoint_pr2.
      rewrite !pathsinv0inv0.
      etrans.
      {
        refine (!_).
        apply pathsdirprod_concat.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply pathsdirprod_concat.
      }
      simpl.
      do 2 apply maponpaths.
      refine (!_).
      apply pathsdirprod_inv.
    - simpl.
      refine (!(pathsinv0l (prod_endpoint_pr2 (comp e₁ (pair e₂ e₃)) x)) @ _).
      apply maponpaths.
      unfold prod_endpoint_pr2.
      simpl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_prod_path.
      }
      apply pathsdirprod_concat.
    - simpl.
      unfold prod_endpoint_pr2 ; simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply pathsinv0inv0.
        }
        apply maponpaths_for_constant_function.
      }
      apply idpath.
    - simpl.
      unfold prod_path_constr.
      etrans.
      {
        exact (maponpaths_pr2_pathsdirprod _ _).
      }
      unfold prod_endpoint_pr2.
      simpl.
      rewrite !pathsinv0inv0.
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      rewrite pathscomp_inv.
      do 2 refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      refine (_ @ path_assoc _ _ _).
      refine (homotsec_natural (alg_path Y j) (prod_endpoint_pr2 _ _) @ _).
      unfold prod_endpoint_pr2.
      rewrite pathsinv0inv0.
      do 2 apply maponpaths.
      apply maponpathsinv0.
    - simpl.
      refine (!_).
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (path_assoc _ _ _ @ _) ; apply maponpaths_2.
        apply pathsinv0l.
      }
      simpl.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
  Qed.
  
  Definition prod_homot_endpoint
             {Q TR : poly_code}
             {al ar : endpoint (point_constr Σ) Q TR}
             {sl sr : endpoint (point_constr Σ) Q I}
             (h : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
             (x : poly_act Q P)
             (p : sem_endpoint_UU al prod_point_constr x
                  =
                  sem_endpoint_UU ar prod_point_constr x)
    : sem_homot_endpoint_one_types
         h
         prod_prealg prod_path_constr
         x p
       =
       pathsdirprod
         (!(prod_endpoint_pr1 sl x)
           @ sem_homot_endpoint_one_types
               h
               _ (alg_path X)
               (poly_map Q pr1 x)
               (prod_endpoint_pr1 _ _
                @ maponpaths (poly_map TR pr1) p
                @ !(prod_endpoint_pr1 _ _))
           @ prod_endpoint_pr1 sr x)
         (!(prod_endpoint_pr2 sl x)
           @ sem_homot_endpoint_one_types
               h
               _ (alg_path Y)
               (poly_map Q (λ (z : P), pr2 z) x)
               (prod_endpoint_pr2 _ _
                @ maponpaths (poly_map TR (λ (z : P), pr2 z)) p
                @ !(prod_endpoint_pr2 _ _))
           @ prod_endpoint_pr2 sr x).
  Proof.
    apply TODO.
  Qed.

  Definition prod_is_alg
    : is_hit_algebra_one_types Σ prod_path_alg.
  Proof.
    intros j x p ; simpl in j, x, p ; cbn in p.
    cbn.
    pose (alg_homot
            X j
            (poly_map (homot_point_arg Σ j) (λ (z : P), pr1 z) x)
            (prod_endpoint_pr1 _ _
             @ maponpaths (poly_map _ (λ (z : P), pr1 z)) p
             @ !(prod_endpoint_pr1 _ _))) as q.
    pose (alg_homot
            Y j
            (poly_map (homot_point_arg Σ j) (λ (z : P), pr2 z) x)
            (prod_endpoint_pr2 _ _
             @ maponpaths (poly_map _ (λ (z : P), pr2 z)) p
             @ !(prod_endpoint_pr2 _ _))) as r.
    refine (pathsdirprod_eta _ @ _ @ !(pathsdirprod_eta _)).
    use paths_pathsdirprod.
    - refine (prod_homot_endpoint_pr1 (homot_left_path Σ j) x p @ _).
      refine (_ @ !(prod_homot_endpoint_pr1 (homot_right_path Σ j) x p)).
      apply maponpaths.
      apply maponpaths_2.
      exact q.
    - refine (prod_homot_endpoint_pr2 (homot_left_path Σ j) x p @ _).
      refine (_ @ !(prod_homot_endpoint_pr2 (homot_right_path Σ j) x p)).
      apply maponpaths.
      apply maponpaths_2.
      exact r.
  Qed.
(*    -
    simple refine
           (prod_homot_endpoint (homot_left_path Σ j) x p
            @ paths_pathsdirprod
                _
                _
            @ !(prod_homot_endpoint (homot_right_path Σ j) x p)).
    - apply maponpaths.
      apply maponpaths_2.
      exact q.
    - apply maponpaths.
      apply maponpaths_2.
      exact r.
  Qed.*)
    
  Definition prod_alg
    : hit_algebra_one_types Σ.
  Proof.
    use make_algebra.
    - exact prod_path_alg.
    - exact prod_is_alg.
  Defined.

  Definition prod_alg_pr1
    : prod_alg --> X.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - use make_hit_prealgebra_mor.
      + exact (λ z, pr1 z).
      + intro ; apply idpath.
    - abstract
        (simpl ;
         intros i x ;
         etrans ;
           [ apply maponpaths_2 ;
             unfold prod_path_constr ;
             exact (maponpaths_pr1_pathsdirprod _ _)
           | unfold prod_endpoint_pr1 ;
             cbn ;
             rewrite pathsinv0inv0 ;
             rewrite <- path_assoc ;
             apply maponpaths ;
             rewrite <- path_assoc ;
             rewrite pathsinv0l ;
             apply pathscomp0rid]).
  Defined.

  Definition prod_alg_pr2
    : prod_alg --> Y.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - use make_hit_prealgebra_mor.
      + exact (λ z, pr2 z).
      + intro ; apply idpath.
    - abstract
        (simpl ;
         intros i x ;
         etrans ;
           [ apply maponpaths_2 ;
             unfold prod_path_constr ;
             exact (maponpaths_pr2_pathsdirprod _ _)
           | unfold prod_endpoint_pr2 ;
             cbn ;
             rewrite pathsinv0inv0 ;
             rewrite <- path_assoc ;
             apply maponpaths ;
             rewrite <- path_assoc ;
             rewrite pathsinv0l ;
             apply pathscomp0rid]).
  Defined.

  Section ProdUMPMap.
    Variable (Z : hit_algebra_one_types Σ)
             (pr1Z : Z --> X)
             (pr2Z : Z --> Y).

    Definition prod_alg_ump_1_constr
               (x : poly_act (point_constr Σ) (prealg_carrier (pr11 Z)))
      : (pr111 pr1Z) (prealg_constr x)
        ,,
        (pr111 pr2Z) (prealg_constr x)
        =
        prod_point_constr
          (poly_map
             (point_constr Σ)
             (λ z : prealg_carrier (pr11 Z), (pr111 pr1Z) z,, (pr111 pr2Z) z)
             x).
    Proof.
      use pathsdirprod.
      - refine (pr1 (pr211 pr1Z) x @ maponpaths (alg_constr X) _) ; cbn.
        exact (!(poly_comp
                   (point_constr Σ)
                   (λ z : prealg_carrier (pr11 Z), (pr111 pr1Z) z,, (pr111 pr2Z) z)
                   (λ z, pr1 z)
                   x)).
      - refine (pr1 (pr211 pr2Z) x @ maponpaths (alg_constr Y) _) ; cbn.
        exact (!(poly_comp
                   (point_constr Σ)
                   (λ z : prealg_carrier (pr11 Z), (pr111 pr1Z) z,, (pr111 pr2Z) z)
                   (λ (z : P), pr2 z)
                   x)).
    Defined.

    Definition maponpaths_pr1_sem_endpoint_UU_natural
               {Q R : poly_code}
               (e : endpoint (point_constr Σ) Q R)
               (x : poly_act Q (path_alg_carrier (pr1 Z)))
      : !(poly_comp _ _ _ _)
        @ maponpaths
            (poly_map R pr1)
            (sem_endpoint_UU_natural e prod_alg_ump_1_constr x)
        =
        sem_endpoint_UU_natural e (pr121 (pr1 pr1Z)) x
        @ maponpaths
            (sem_endpoint_UU e (pr211 X))
            (!(poly_comp
                 Q
                 (λ z : prealg_carrier (pr11 Z), (pr111 pr1Z) z,, (pr111 pr2Z) z)
                 (λ (z : P), pr1 z)
                 x))
        @ prod_endpoint_pr1 _ _.
    Proof.
      induction e as [Q | Q₁ Q₂ Q₃ e₁ IHe₁ e₂ IHe₂
                      | Q R | Q R | Q R | Q R
                      | Q₁ Q₂ Q₃ e₁ IHe₁ e₂ IHe₂
                      | Q T t | C₁ C₂ g | ].
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        apply maponpathsidfun.
      - unfold prod_endpoint_pr1 ; simpl.
        refine (!_).
        etrans.
        {
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
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply maponpathscomp.
            }
            refine (!_).
            apply maponpathscomp0.
          }
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply maponpathsinv0.
          }
          etrans.
          {
            refine (!_).
            apply maponpathscomp0.
          }
          apply maponpaths.
          refine (!(path_assoc _ _ _) @ _).
          refine (!_).
          apply IHe₁.
        }
        clear IHe₁.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply (maponpathscomp0 (poly_map Q₃ pr1)).
        }
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply IHe₂.
        }
        clear IHe₂.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
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
          apply (maponpathscomp (poly_map Q₂ pr1) (sem_endpoint_UU e₂ (alg_constr X))).
        }
        etrans.
        {
          apply (homotsec_natural' (prod_endpoint_pr1 e₂)).
        }
        apply maponpaths.
        refine (!_).
        apply maponpathscomp.
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        apply (maponpathsinv0 inl).
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        apply (maponpathsinv0 inr).
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        etrans.
        {
          exact (maponpathsinv0 pr1 (pathsdirprod _ _)).
        }
        apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        etrans.
        {
          exact (maponpathsinv0 dirprod_pr2 (pathsdirprod _ _)).
        }
        apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
      - unfold prod_endpoint_pr1.
        simpl.
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
            refine (!_).
            apply maponpaths_pathsdirprod.
          }
          apply pathsdirprod_concat.
        }
        refine (!_).
        etrans.
        {
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
        refine (!_).
        exact (paths_pathsdirprod (IHe₁ x) (IHe₂ x)).
      - simpl ; cbn.
        refine (!_).
        refine (pathscomp0rid _ @ _).
        apply maponpaths_for_constant_function.
      - apply idpath.
      - simpl ; cbn.
        etrans.
        {
          apply maponpaths_pr1_pathsdirprod.
        }
        refine (!_).
        apply maponpaths.
        apply pathscomp0rid.
    Qed.

    Definition maponpaths_pr2_sem_endpoint_UU_natural
               {Q R : poly_code}
               (e : endpoint (point_constr Σ) Q R)
               (x : poly_act Q (path_alg_carrier (pr1 Z)))
      : !(poly_comp _ _ _ _)
        @ maponpaths
            (poly_map R dirprod_pr2)
            (sem_endpoint_UU_natural e prod_alg_ump_1_constr x)
        =
        sem_endpoint_UU_natural e (pr121 (pr1 pr2Z)) x
        @ maponpaths
            (sem_endpoint_UU e (pr211 Y))
            (!(poly_comp
                 Q
                 (λ z : prealg_carrier (pr11 Z), (pr111 pr1Z) z,, (pr111 pr2Z) z)
                 (λ (z : P), pr2 z)
                 x))
        @ prod_endpoint_pr2 _ _.
    Proof.
      induction e as [Q | Q₁ Q₂ Q₃ e₁ IHe₁ e₂ IHe₂
                      | Q R | Q R | Q R | Q R
                      | Q₁ Q₂ Q₃ e₁ IHe₁ e₂ IHe₂
                      | Q T t | C₁ C₂ g | ].
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        apply maponpathsidfun.
      - unfold prod_endpoint_pr2 ; simpl.
        refine (!_).
        etrans.
        {
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
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              refine (!_).
              apply maponpathscomp.
            }
            refine (!_).
            apply maponpathscomp0.
          }
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply maponpathsinv0.
          }
          etrans.
          {
            refine (!_).
            apply maponpathscomp0.
          }
          apply maponpaths.
          refine (!(path_assoc _ _ _) @ _).
          refine (!_).
          apply IHe₁.
        }
        clear IHe₁.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply (maponpathscomp0 (poly_map Q₃ dirprod_pr2)).
        }
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply IHe₂.
        }
        clear IHe₂.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
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
                   (poly_map Q₂ dirprod_pr2)
                   (sem_endpoint_UU e₂ (alg_constr Y))).
        }
        etrans.
        {
          apply (homotsec_natural' (prod_endpoint_pr2 e₂)).
        }
        apply maponpaths.
        refine (!_).
        apply maponpathscomp.
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        apply (maponpathsinv0 inl).
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        apply (maponpathsinv0 inr).
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        etrans.
        {
          exact (maponpathsinv0 pr1 (pathsdirprod _ _)).
        }
        apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
      - refine (pathscomp0rid _ @ _ @ !(pathscomp0rid _)) ; simpl.
        refine (!_).
        etrans.
        {
          exact (maponpathsinv0 dirprod_pr2 (pathsdirprod _ _)).
        }
        apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
      - unfold prod_endpoint_pr2.
        simpl.
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
            refine (!_).
            apply maponpaths_pathsdirprod.
          }
          apply pathsdirprod_concat.
        }
        refine (!_).
        etrans.
        {
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
        refine (!_).
        exact (paths_pathsdirprod (IHe₁ x) (IHe₂ x)).
      - simpl ; cbn.
        refine (!_).
        refine (pathscomp0rid _ @ _).
        apply maponpaths_for_constant_function.
      - apply idpath.
      - simpl ; cbn.
        etrans.
        {
          apply maponpaths_pr2_pathsdirprod.
        }
        refine (!_).
        apply maponpaths.
        apply pathscomp0rid.
    Qed.
    
    Definition prod_alg_ump_1_path
               (i : path_label Σ)
               (x : poly_act (path_source Σ i) (path_alg_carrier (pr1 Z)))
      : maponpaths
          (λ z, (pr111 pr1Z) z,, (pr111 pr2Z) z)
          ((pr21 Z) i x)
        @ sem_endpoint_UU_natural (path_right Σ i) prod_alg_ump_1_constr x
        =
        sem_endpoint_UU_natural (path_left Σ i) prod_alg_ump_1_constr x
        @ prod_path_constr
            i
            (poly_map
               (path_source Σ i)
               (λ z, (pr111 pr1Z) z,, (pr111 pr2Z) z) x).
    Proof.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_prod_path.
      }
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_eta.
      }
      etrans.
      {
        exact (pathsdirprod_concat _ _ _ _).
      }      
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply pathsdirprod_eta.
      }
      etrans.
      {
        exact (pathsdirprod_concat _ _ _ _).
      }
      use paths_pathsdirprod.
      - simpl.
        unfold prod_endpoint_pr1.
        rewrite pathsinv0inv0.
        pose (eqtohomot (pr21 pr1Z i) x) as m.
        cbn in m.
        unfold homotcomp, homotfun, funhomotsec in m.
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            exact (maponpaths_pr1_sem_endpoint_UU_natural (path_right Σ i) x).
          }
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          exact m.
        }
        rewrite <- !path_assoc.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (maponpaths_pr1_sem_endpoint_UU_natural (path_left Σ i) x).
        }
        rewrite <- !path_assoc.
        apply maponpaths.
        rewrite !path_assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite <- path_assoc.
          etrans.
          {
            apply maponpaths.
            apply pathsinv0l.
          }
          apply pathscomp0rid.
        }
        apply (homotsec_natural' (alg_path X i)).
      - simpl.
        unfold prod_endpoint_pr2.
        rewrite pathsinv0inv0.
        pose (eqtohomot (pr21 pr2Z i) x) as m.
        cbn in m.
        unfold homotcomp, homotfun, funhomotsec in m.
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            exact (maponpaths_pr2_sem_endpoint_UU_natural (path_right Σ i) x).
          }
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          exact m.
        }
        rewrite <- !path_assoc.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (maponpaths_pr2_sem_endpoint_UU_natural (path_left Σ i) x).
        }
        rewrite <- !path_assoc.
        apply maponpaths.
        rewrite !path_assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite <- path_assoc.
          etrans.
          {
            apply maponpaths.
            apply pathsinv0l.
          }
          apply pathscomp0rid.
        }
        apply (homotsec_natural' (alg_path Y i)).
    Time Qed.

    Definition prod_alg_ump_1
      : Z --> prod_alg.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - use make_hit_prealgebra_mor.
        + exact (λ z, pr111 pr1Z z ,, pr111 pr2Z z).
        + exact prod_alg_ump_1_constr.
      - exact prod_alg_ump_1_path.
    Defined.

    Definition prod_alg_ump_1_pr1
      : prod_alg_ump_1 · prod_alg_pr1 ==> pr1Z.
    Proof.
      simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
      - exact (λ _, idpath _).
      - abstract
          (use funextsec ;
           intro z ; cbn ;
           unfold homotcomp, funhomotsec, homotfun ;
           cbn ;
           rewrite !pathscomp0rid ;
           refine (!_) ;
           refine (maponpaths
                     (λ z, (z @ _) @ _)
                     (maponpaths_pr1_pathsdirprod _ _)
                     @ _) ;
           rewrite <- !path_assoc ;
           etrans ;
           [ apply maponpaths ;
             rewrite path_assoc ;
             apply maponpaths_2 ;
             etrans ;
             [ refine (!_) ;
               apply (maponpathscomp0 (alg_constr X))
             | apply maponpaths ;
               apply pathsinv0l ]
           | simpl ;
             etrans ;
             [ do 2 apply maponpaths ;
               apply (eqtohomot (psfunctor_id2 (⟦ point_constr Σ ⟧) (pr111 pr1Z)))
             | apply pathscomp0rid ]]).
    Defined.

    Definition prod_alg_ump_1_pr2
      : prod_alg_ump_1 · prod_alg_pr2 ==> pr2Z.
    Proof.
      simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
      - exact (λ _, idpath _).
      - abstract
          (use funextsec ;
           intro z ; cbn ;
           unfold homotcomp, funhomotsec, homotfun ;
           cbn ;
           rewrite !pathscomp0rid ;
           refine (!_) ;
           refine (maponpaths
                     (λ z, (z @ _) @ _)
                     (maponpaths_pr2_pathsdirprod _ _)
                     @ _) ;
           rewrite <- !path_assoc ;
           etrans ;
           [ apply maponpaths ;
             rewrite path_assoc ;
             apply maponpaths_2 ;
             etrans ;
             [ refine (!_) ;
               apply (maponpathscomp0 (alg_constr Y))
             | apply maponpaths ;
               apply pathsinv0l ]
           | simpl ;
             etrans ;
             [ do 2 apply maponpaths ;
               apply (eqtohomot (psfunctor_id2 (⟦ point_constr Σ ⟧) (pr111 pr2Z)))
             | apply pathscomp0rid ]]).
    Defined.
  End ProdUMPMap.

  Section ProdUMPCell.
    Context {Z : hit_algebra_one_types Σ}
            {pr1Z : Z --> X}
            {pr2Z : Z --> Y}
            (φ ψ : Z --> prod_alg)
            (φpr1 : φ · prod_alg_pr1 ==> pr1Z)
            (φpr2 : φ · prod_alg_pr2 ==> pr2Z)
            (ψpr1 : ψ · prod_alg_pr1 ==> pr1Z)
            (ψpr2 : ψ · prod_alg_pr2 ==> pr2Z).

    Local Definition prod_alg_ump_2_comp
      : alg_map_carrier φ ~ alg_map_carrier ψ.
    Proof.
      intro x.
      use pathsdirprod.
      - exact (pr111 φpr1 x @ !(pr111 ψpr1 x)).
      - exact (pr111 φpr2 x @ !(pr111 ψpr2 x)).
    Defined.

    Local Definition prod_alg_ump_2_is_alg_2cell
      : is_algebra_2cell prod_alg_ump_2_comp.
    Proof.
      intro x.
      cbn ; unfold  prod_alg_ump_2_comp, alg_map_commute.
      refine (_ @ !(pathsdirprod_eta _)).
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_eta.
      }
      etrans.
      {
        apply pathsdirprod_concat.
      }
      use paths_pathsdirprod.
      - pose (eqtohomot (pr211 φpr1) x) as p.
        cbn in p.
        unfold homotcomp, homotfun, funhomotsec in p.
        cbn in p.
        rewrite !pathscomp0rid in p.
        pose (maponpaths (λ z, !z) (eqtohomot (pr211 ψpr1) x)) as q.
        cbn in q.
        unfold homotcomp, homotfun, funhomotsec in q.
        cbn in q.
        rewrite !pathscomp0rid in q.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {            
            apply maponpaths_2.
            etrans.
            {
              etrans.
              {
                exact (!(pathscomp0rid _)).
              }
              apply maponpaths.
              exact (!(pathsinv0r (alg_map_commute pr1Z x))).
            }
            refine (path_assoc _ _ _ @ _).
            apply maponpaths_2.
            exact p.
          }
          refine (!(path_assoc _ _ _) @ _).
          apply maponpaths.
          etrans.
          {
            exact (!(pathscomp_inv _ _)).
          }
          etrans.
          {
            exact q.
          }
          etrans.
          {
            apply pathscomp_inv.
          }
          apply maponpaths.
          apply pathscomp_inv.
        }
        do 3 refine (!(path_assoc _ _ _) @ _).
        refine (!_).
        etrans.
        {
          exact (maponpathscomp0
                   pr1
                   (alg_map_commute φ x)
                   (maponpaths
                      prod_point_constr
                      (poly_homot _ _ _))).
        }
        apply maponpaths.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          refine (!(path_assoc _ _ _) @ _) ; apply maponpaths.
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0l.
          }
          apply pathscomp0rid.
        }
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (!_).
                apply maponpathsinv0.
              }
              etrans.
              {
                apply maponpaths_2.
                refine (!_).
                apply maponpathsinv0.
              }
              refine (!_).
              apply maponpathscomp0.
            }
            refine (!_).
            apply maponpathscomp0.
          }
          refine (!_).
          apply (maponpathscomp0 (alg_constr X)).
        }
        refine (!_).
        etrans.
        {
          apply maponpathscomp.
        }
        unfold funcomp ; cbn.
        etrans.
        {
          refine (!_).
          apply maponpathscomp.
        }
        apply maponpaths.
        etrans.
        {
          apply poly_homot_pathsdirprod_pr1.
        }
        apply maponpaths.
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        etrans.
        {
          pose (eqtohomot
                  (psfunctor_vcomp
                     (⟦ point_constr Σ ⟧)
                     (pr111 φpr1)
                     (invhomot (pr111 ψpr1)))
                  x)
            as r.
          cbn in r ; unfold homotcomp, invhomot in r.
          exact r.
        }
        apply maponpaths.
        apply poly_homot_inv.
      - pose (eqtohomot (pr211 φpr2) x) as p.
        cbn in p.
        unfold homotcomp, homotfun, funhomotsec in p.
        cbn in p.
        rewrite !pathscomp0rid in p.
        pose (maponpaths (λ z, !z) (eqtohomot (pr211 ψpr2) x)) as q.
        cbn in q.
        unfold homotcomp, homotfun, funhomotsec in q.
        cbn in q.
        rewrite !pathscomp0rid in q.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {            
            apply maponpaths_2.
            etrans.
            {
              etrans.
              {
                exact (!(pathscomp0rid _)).
              }
              apply maponpaths.
              exact (!(pathsinv0r (alg_map_commute pr2Z x))).
            }
            refine (path_assoc _ _ _ @ _).
            apply maponpaths_2.
            exact p.
          }
          refine (!(path_assoc _ _ _) @ _).
          apply maponpaths.
          etrans.
          {
            exact (!(pathscomp_inv _ _)).
          }
          etrans.
          {
            exact q.
          }
          etrans.
          {
            apply pathscomp_inv.
          }
          apply maponpaths.
          apply pathscomp_inv.
        }
        do 3 refine (!(path_assoc _ _ _) @ _).
        refine (!_).
        etrans.
        {
          exact (maponpathscomp0
                   dirprod_pr2
                   (alg_map_commute φ x)
                   (maponpaths
                      prod_point_constr
                      (poly_homot _ _ _))).
        }
        apply maponpaths.
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          refine (!(path_assoc _ _ _) @ _) ; apply maponpaths.
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0l.
          }
          apply pathscomp0rid.
        }
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                refine (!_).
                apply maponpathsinv0.
              }
              etrans.
              {
                apply maponpaths_2.
                refine (!_).
                apply maponpathsinv0.
              }
              refine (!_).
              apply maponpathscomp0.
            }
            refine (!_).
            apply maponpathscomp0.
          }
          refine (!_).
          apply (maponpathscomp0 (alg_constr Y)).
        }
        refine (!_).
        etrans.
        {
          apply maponpathscomp.
        }
        unfold funcomp ; cbn.
        etrans.
        {
          refine (!_).
          apply maponpathscomp.
        }
        apply maponpaths.
        etrans.
        {
          apply poly_homot_pathsdirprod_pr2.
        }
        apply maponpaths.
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        etrans.
        {
          pose (eqtohomot
                  (psfunctor_vcomp
                     (⟦ point_constr Σ ⟧)
                     (pr111 φpr2)
                     (invhomot (pr111 ψpr2)))
                  x)
            as r.
          cbn in r ; unfold homotcomp, invhomot in r.
          exact r.
        }
        apply maponpaths.
        apply poly_homot_inv.
    Qed.

    Definition prod_alg_ump_2
      : φ ==> ψ.
    Proof.
      use make_algebra_2cell.
      - exact prod_alg_ump_2_comp.
      - exact prod_alg_ump_2_is_alg_2cell.
    Defined.

    Definition prod_alg_ump_2_pr1
      : (prod_alg_ump_2 ▹ prod_alg_pr1) • ψpr1 = φpr1.
    Proof.
      use subtypePath.
      { intro ; apply isapropunit. }
      use subtypePath.
      { intro ; use impred ; intro ; apply isapropunit. }
      use subtypePath.
      { intro ; apply one_types. }
      simpl ; cbn ; unfold homotcomp, homotfun.
      use funextsec.
      intro x ; cbn.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_pr1_pathsdirprod.
      }
      rewrite <- path_assoc.
      rewrite pathsinv0l.
      apply pathscomp0rid.
    Qed.

    Definition prod_alg_ump_2_pr2
      : (prod_alg_ump_2 ▹ prod_alg_pr2) • ψpr2 = φpr2.
    Proof.
      use subtypePath.
      { intro ; apply isapropunit. }
      use subtypePath.
      { intro ; use impred ; intro ; apply isapropunit. }
      use subtypePath.
      { intro ; apply one_types. }
      simpl ; cbn ; unfold homotcomp, homotfun.
      use funextsec.
      intro x ; cbn.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_pr2_pathsdirprod.
      }
      rewrite <- path_assoc.
      rewrite pathsinv0l.
      apply pathscomp0rid.
    Qed.
  End ProdUMPCell.
    
  Section ProdUMPEq.
    Context {Z : hit_algebra_one_types Σ}
            {pr1Z : Z --> X}
            {pr2Z : Z --> Y}
            {φ ψ : Z --> prod_alg}
            {φpr1 : φ · prod_alg_pr1 ==> pr1Z}
            {φpr2 : φ · prod_alg_pr2 ==> pr2Z}
            {ψpr1 : ψ · prod_alg_pr1 ==> pr1Z}
            {ψpr2 : ψ · prod_alg_pr2 ==> pr2Z}
            (τ θ : φ ==> ψ)
            (τpr1 : (τ ▹ prod_alg_pr1) • ψpr1 = φpr1)
            (τpr2 : (τ ▹ prod_alg_pr2) • ψpr2 = φpr2)
            (θpr1 : (θ ▹ prod_alg_pr1) • ψpr1 = φpr1)
            (θpr2 : (θ ▹ prod_alg_pr2) • ψpr2 = φpr2).

    Definition prod_ump_eq
      : τ = θ.
    Proof.
      use subtypePath.
      { intro ; apply isapropunit. }
      use subtypePath.
      { intro ; use impred ; intro ; apply isapropunit. }
      use subtypePath.
      { intro ; apply one_types. }
      simpl ; cbn ; unfold homotcomp, homotfun.
      use funextsec.
      intro x ; cbn.
      refine (pathsdirprod_eta _ @ _ @ !(pathsdirprod_eta _)).
      apply paths_pathsdirprod.
      - refine (!(maponpaths _ (pathsinv0r _) @ pathscomp0rid _) @ path_assoc _ _ _
                @ maponpaths
                    (λ z, z @ !(pr111 ψpr1 x))
                    (eqtohomot (maponpaths (λ z, pr111 z) τpr1) x)
                @ maponpaths
                    (λ z, z @ !(pr111 ψpr1 x))
                    (!(eqtohomot (maponpaths (λ z, pr111 z) θpr1) x))
                @ _).
        cbn ; unfold homotcomp, homotfun.
        exact (!(path_assoc _ _ _) @ maponpaths _ (pathsinv0r _) @ pathscomp0rid _).
      - refine (!(maponpaths _ (pathsinv0r _) @ pathscomp0rid _) @ path_assoc _ _ _
                @ maponpaths
                    (λ z, z @ !(pr111 ψpr2 x))
                    (eqtohomot (maponpaths (λ z, pr111 z) τpr2) x)
                @ maponpaths
                    (λ z, z @ !(pr111 ψpr2 x))
                    (!(eqtohomot (maponpaths (λ z, pr111 z) θpr2) x))
                @ _).
        cbn ; unfold homotcomp, homotfun.
        exact (!(path_assoc _ _ _) @ maponpaths _ (pathsinv0r _) @ pathscomp0rid _).
    Qed.
  End ProdUMPEq.  
End ProductAlg.
