(**
Biadjunction when adding a 2-cell to the algebra structure
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.

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
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.groupoid_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.groupoid_homotopies.
Require Import biadjunctions.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import hit_biadjunction.gquot_natural.
Require Import hit_biadjunction.hit_prealgebra_biadj.
Require Import hit_biadjunction.hit_path_algebra_biadj.
Require Import hit_biadjunction.hit_path_algebra_biadj.unit.

Local Open Scope cat.

Definition gquot_endpoint_help_gcl
           {A S T : poly_code}
           (e : endpoint A S T)
           (G : total_bicat (disp_alg_bicat ⦃ A ⦄))
           (x : poly_act_groupoid S (pr1 G))
  : sem_endpoint_UU
      e
      (prealg_gquot_map A (pr1 G) (pr2 G))
      (gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x))
    =
    gquot_poly
      (gcl (poly_act_groupoid T (pr1 G))
           (sem_endpoint_UU e (λ z, pr12 G z) x)).
Proof.
  exact (@gquot_endpoint_help
          _ _ _
          e G
          (gcl _ x)).
Defined.

Definition sem_homot_endpoint_one_types_gquot_poly_poly_gquot_help
           {A B C : UU}
           {l r : A → B}
           {fl fr : A → C}
           (g : ∏ (a : A), l a = r a → fl a = fr a)
           {a₁ a₂ : A}
           (p : a₂ = a₁)
           (q : l a₁ = r a₁)
  : g a₁ q
    =
    maponpaths fl (!p)
    @ g a₂ (maponpaths l p @ q @ maponpaths r (!p))
    @ maponpaths fr p.
Proof.
  induction p ; cbn.
  refine (!_).
  etrans.
  {
    apply pathscomp0rid.
  }
  apply maponpaths.
  apply pathscomp0rid.
Defined.

Definition sem_homot_endpoint_one_types_gquot_poly_poly_gquot
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l : ∏ (j : J), endpoint A (S j) I}
           {r : ∏ (j : J), endpoint A (S j) I}
           {Q : poly_code}
           {TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : poly_code}
           {sl sr : endpoint A Q T}
           (p : homot_endpoint l r al ar sl sr)
           (G : total_bicat (disp_alg_bicat ⦃ A ⦄))
           (pG : ∏ (j : J),
                 sem_endpoint_grpd_data_functor_data (l j) G
                 ⟹
                 sem_endpoint_grpd_data_functor_data (r j) G)
           (x : poly_act Q (gquot (pr1 G)))
           (y : (sem_endpoint_one_types al) ((total_prealg_gquot A) G) x
                =
                (sem_endpoint_one_types ar) ((total_prealg_gquot A) G) x)
  : sem_homot_endpoint_one_types
      p
      (total_prealg_gquot A G)
      (λ j, lift_gquot_add2cell (l j) (r j) G (pG j))
      x
      y
    =
    maponpaths
      ((sem_endpoint_one_types sl) ((total_prealg_gquot A) G))
      (!(gquot_poly_poly_gquot _))
    @ sem_homot_endpoint_one_types
        p
        (total_prealg_gquot A G)
        (λ j, lift_gquot_add2cell (l j) (r j) G (pG j))
        (gquot_poly (poly_gquot _ _ x))
        (maponpaths
           ((sem_endpoint_one_types al) ((total_prealg_gquot A) G))
           (gquot_poly_poly_gquot _)
         @ y
         @ maponpaths
             ((sem_endpoint_one_types ar) ((total_prealg_gquot A) G))
             (!(gquot_poly_poly_gquot _))
        )
    @ maponpaths
        ((sem_endpoint_one_types sr) ((total_prealg_gquot A) G))
        (gquot_poly_poly_gquot x).
Proof.
  apply sem_homot_endpoint_one_types_gquot_poly_poly_gquot_help.
Qed.

Definition path_arg_to_mor_help
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (p : poly_map P (gcl G) x = poly_map P (gcl G) y)
  : poly_act_morphism P G x y.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact p.
  - exact (encode_gquot _ _ _ p).
  - induction x as [x | x], y as [y | y].
    + apply IHP₁.
      exact (ii1_injectivity _ _ p).
    + apply fromempty.
      exact (negpathsii1ii2 _ _ p).
    + apply fromempty.
      exact (negpathsii2ii1 _ _ p).
    + apply IHP₂.
      exact (ii2_injectivity _ _ p).
  - exact (IHP₁ _ _ (maponpaths pr1 p)
           ,,
           IHP₂ _ _ (maponpaths dirprod_pr2 p)).
Defined.

Definition path_arg_to_mor
           {A S T : poly_code}
           {al ar : endpoint A S T}
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (x : poly_act_groupoid S (pr1 G))
           (y : sem_endpoint_UU
                  al
                  (prealg_gquot_map A (pr1 G) (pr2 G))
                  (gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x))
                =
                sem_endpoint_UU
                  ar
                  (prealg_gquot_map A (pr1 G) (pr2 G))
                  (gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x)))
  : poly_act_morphism
      T
      (pr1 G)
      (sem_endpoint_UU al (pr12 G) x)
      (sem_endpoint_UU ar (pr12 G) x).
Proof.
  pose (!gquot_endpoint_help al (gcl (poly_act_groupoid S (pr1 G)) x)
         @ y
         @ gquot_endpoint_help ar (gcl (poly_act_groupoid S (pr1 G)) x))
    as p.
  pose (poly_map_gcl_is_gquot_poly _
        @ p
        @ !(poly_map_gcl_is_gquot_poly _))
    as q.
  exact (path_arg_to_mor_help q).
Defined.

Definition sem_homot_endpoint_one_types_sem_homot_endpoint_grpd_path_arg
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (p : gquot_poly (gcl (poly_act_groupoid P G) x)
                =
                gquot_poly (gcl (poly_act_groupoid P G) y))
  : p
    =
    maponpaths
      gquot_poly
      (gcleq
         (poly_act_groupoid P G)
         (path_arg_to_mor_help
            (poly_map_gcl_is_gquot_poly x
             @ p
             @ !(poly_map_gcl_is_gquot_poly y)))).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    apply pathscomp0rid.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply pathscomp0rid.
    }
    exact (@decode_gquot_encode_gquot
             G
             (gcl G x) (gcl G y)
             p).
  - induction x as [x | x], y as [y | y].
    + simpl.
      refine (!_).
      etrans.
      {
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      simpl.
      refine (_ @ inl_ii1_injectivity _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply IHP₁.
      }
      etrans.
      {
        apply maponpathscomp.
      }
      do 3 apply maponpaths.
      refine (!_).
      etrans.
      {
        apply ii1_injectivity_concat.
      }
      etrans.
      {
        apply maponpaths.
        apply ii1_injectivity_concat.
      }
      etrans.
      {
        apply maponpaths_2.
        apply ii1_injectivity_inl.
      }
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathsinv0.
      }
      apply ii1_injectivity_inl.
    + exact (fromempty (negpathsii1ii2 _ _ p)).
    + exact (fromempty (negpathsii2ii1 _ _ p)).
    + simpl.
      refine (!_).
      etrans.
      {
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      simpl.
      refine (_ @ inr_ii2_injectivity _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply IHP₂.
      }
      etrans.
      {
        apply maponpathscomp.
      }
      do 3 apply maponpaths.
      refine (!_).
      etrans.
      {
        apply ii2_injectivity_concat.
      }
      etrans.
      {
        apply maponpaths.
        apply ii2_injectivity_concat.
      }
      etrans.
      {
        apply maponpaths_2.
        apply ii2_injectivity_inr.
      }
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathsinv0.
      }
      apply ii2_injectivity_inr.
  - simpl.
    refine (!_).
    etrans.
    {
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    simpl.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        do 3 apply maponpaths.
        etrans.
        {
          exact (maponpathscomp0
                   pr1
                   (pathsdirprod _ _)
                   (p @ ! pathsdirprod _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths_pr1_pathsdirprod.
        }
        apply maponpaths.
        etrans.
        {
          exact (maponpathscomp0
                   pr1
                   p
                   (! pathsdirprod _ _)).
        }
        apply maponpaths.
        etrans.
        {
          apply maponpathsinv0.
        }
        apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
      }
      etrans.
      {
        do 4 apply maponpaths.
        etrans.
        {
          exact (maponpathscomp0
                   dirprod_pr2
                   (pathsdirprod _ _)
                   (p @ ! pathsdirprod _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths_pr2_pathsdirprod.
        }
        apply maponpaths.
        etrans.
        {
          exact (maponpathscomp0
                   dirprod_pr2
                   p
                   (! pathsdirprod _ _)).
        }
        apply maponpaths.
        etrans.
        {
          apply maponpathsinv0.
        }
        apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
      }
      exact (!(paths_pathsdirprod
                 (IHP₁ _ _ (maponpaths pr1 p))
                 (IHP₂ _ _ (maponpaths dirprod_pr2 p)))).
    }
    refine (!_).
    exact (pathsdirprod_eta p).
Qed.

Definition sem_homot_endpoint_one_types_sem_homot_endpoint_grpd
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l : ∏ (j : J), endpoint A (S j) I}
           {r : ∏ (j : J), endpoint A (S j) I}
           {Q : poly_code}
           {TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : poly_code}
           {sl sr : endpoint A Q T}
           (p : homot_endpoint l r al ar sl sr)
           (G : total_bicat (disp_alg_bicat ⦃ A ⦄))
           (pG : ∏ (j : J),
                 sem_endpoint_grpd_data_functor_data (l j) G
                 ⟹
                 sem_endpoint_grpd_data_functor_data (r j) G)
           (x : poly_act_groupoid Q (pr1 G))
           (y : (sem_endpoint_one_types al)
                  ((total_prealg_gquot A) G)
                  (gquot_poly (gcl (poly_act_groupoid Q (pr1 G)) x))
                =
                (sem_endpoint_one_types ar)
                  ((total_prealg_gquot A) G)
                  (gquot_poly (gcl (poly_act_groupoid Q (pr1 G)) x)))
  : sem_homot_endpoint_one_types
      p
      (total_prealg_gquot A G)
      (λ j, lift_gquot_add2cell (l j) (r j) G (pG j))
      (gquot_poly (gcl _ x))
      y
    =
    gquot_endpoint_help_gcl sl G x
    @ maponpaths
        gquot_poly
        (gcleq
           _
           (sem_homot_endpoint_grpd
              p
              G
              pG
              x
              (path_arg_to_mor x y)))
    @ !(gquot_endpoint_help_gcl sr G x).
Proof.
  unfold gquot_endpoint_help_gcl.
  induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | T₁ T₂ e₁ e₂ e₃ e₄ p IHp | T₁ T₂ e₁ e₂ e₃ e₄ p IHp
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - (* identity *)
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply ge.
    }
    apply pathsinv0r.
  - (* symmetry *)
    simpl.
    etrans.
    {
      exact (maponpaths (λ z, ! z) IHp).
    }
    etrans.
    {
      apply pathscomp_inv.
    }
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    etrans.
    {
      apply pathscomp_inv.
    }
    etrans.
    {
      apply maponpaths_2.
      apply pathsinv0inv0.
    }
    apply maponpaths.
    etrans.
    {
      refine (!_).
      apply maponpathsinv0.
    }
    apply maponpaths.
    etrans.
    {
      refine (!_).
      apply ginv.
    }
    apply maponpaths.
    apply poly_act_id_right.
  - (* transitivity *)
    simpl.
    etrans.
    {
      apply maponpaths_2.
      exact IHP₁.
    }
    etrans.
    {
      apply maponpaths.
      exact IHP₂.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0l.
    }
    simpl.
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    apply maponpaths.
    refine (!_).
    apply gconcat.
  - (* associativity *)
    simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply ge.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply pathscomp0lid.
      }
      apply pathscomp_inv.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0r.
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        exact (maponpathscomp
                 (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))
                 (sem_endpoint_UU e₃ (prealg_gquot_map A (pr1 G) (pr2 G)))
                 (gquot_endpoint_help_gcl e₁ G x)).
      }
      refine (!_).
      apply (maponpathscomp0
               (sem_endpoint_UU e₃ (prealg_gquot_map A (pr1 G) (pr2 G)))).
    }
    apply pathsinv0r.
  - (* left identity *)
    simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply ge.
    }
    apply pathsinv0r.
  - (* right identity *)
    simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply pathscomp0rid.
      }
      apply maponpathsidfun.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply ge.
    }
    apply pathsinv0r.
  - (* first projection *)
    simpl ; simpl in IHp.
    etrans.
    {
      apply maponpaths.
      apply IHp.
    }
    etrans.
    {
      etrans.
      {
        exact (maponpathscomp0
                 pr1
                 (pathsdirprod _ _)
                 (_ @ !(pathsdirprod _ _))).
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_pr1_pathsdirprod.
      }
      apply maponpaths.
      etrans.
      {
        exact (maponpathscomp0
                 pr1
                 (maponpaths
                    (gquot_prod gquot_poly gquot_poly)
                    (gcleq _ (sem_homot_endpoint_grpd p G pG x _)))
                 (!(pathsdirprod _ _))).
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_inv.
      }
      apply maponpaths_pr1_pathsdirprod.
    }
    apply maponpaths.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    apply maponpaths_pr1_pathsdirprod.
  - (* second projection *)
    simpl ; simpl in IHp.
    etrans.
    {
      apply maponpaths.
      apply IHp.
    }
    etrans.
    {
      etrans.
      {
        exact (maponpathscomp0
                 dirprod_pr2
                 (pathsdirprod _ _)
                 (_ @ !(pathsdirprod _ _))).
      }
      simpl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_pr2_pathsdirprod.
      }
      apply maponpaths.
      etrans.
      {
        exact (maponpathscomp0
                 dirprod_pr2
                 (maponpaths
                    (gquot_prod gquot_poly gquot_poly)
                    (gcleq _ (sem_homot_endpoint_grpd p G pG x _)))
                 (!(pathsdirprod _ _))).
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_inv.
      }
      apply maponpaths_pr2_pathsdirprod.
    }
    apply maponpaths.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    apply maponpaths_pr2_pathsdirprod.
  - (* pair of endpoints *)
    simpl.
    etrans.
    {
      exact (paths_pathsdirprod IHp₁ IHp₂).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
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
  - (* left inclusion *)
    simpl.
    etrans.
    {
      apply maponpaths.
      exact IHp.
    }
    etrans.
    {
      apply (maponpathscomp0 inl).
    }
    etrans.
    {
      apply maponpaths.
      apply (maponpathscomp0 inl).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpathsinv0.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply pathscomp0rid.
    }
    etrans.
    {
      do 3 apply maponpaths.
      apply pathscomp0rid.
    }
    apply maponpaths.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpathscomp.
    }
    refine (!_).
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - (* right inclusion *)
    simpl.
    etrans.
    {
      apply maponpaths.
      exact IHp.
    }
    etrans.
    {
      apply (maponpathscomp0 inr).
    }
    etrans.
    {
      apply maponpaths.
      apply (maponpathscomp0 inr).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpathsinv0.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply pathscomp0rid.
    }
    etrans.
    {
      do 3 apply maponpaths.
      apply pathscomp0rid.
    }
    apply maponpaths.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpathscomp.
    }
    refine (!_).
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - (* path constructor *)
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (gquot_rec_beta_gcleq
               _ _ _ _ _ _ _ _ _
               (pG j (sem_endpoint_UU e (pr12 G) x))).
    }
    simpl.
    unfold lift_gquot_add2cell_obj.
    refine (!_).
    unfold gquot_endpoint.
    etrans.
    {
      do 2 apply maponpaths.
      apply pathscomp_inv.
    }

    pose (f := λ z,
               gquot_endpoint_help
                 (l j)
                 z
               @ maponpaths
                   gquot_poly
                   (@gquot_functor_cell
                      _ _
                      (sem_endpoint_grpd_data_functor (l j) G)
                      (sem_endpoint_grpd_data_functor (r j) G)
                      (pG j)
                      z)
               @ !(gquot_endpoint_help
                     (r j)
                     z)).
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        refine (!_).
        apply (maponpathsinv0
                 ((sem_endpoint_one_types (r j)) ((total_prealg_gquot A) G))).
      }
      apply maponpaths.
      apply pathsinv0inv0.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (homotsec_natural
               f
               (!(maponpaths
                    (poly_gquot (S j) (pr1 G))
                    (gquot_endpoint_help_gcl _ _ _ )
                  @ poly_gquot_gquot_poly _))).
    }
    unfold f.
    simpl.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      do 2 refine (path_assoc _ _ _ @ _).
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply pathsinv0inv0.
      }
      cbn.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathscomp.
      }
      etrans.
      {
        refine (!_).
        apply maponpathscomp0.
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths_2.
        etrans.
        {
          apply maponpathscomp.
        }
        apply (maponpaths_homot gquot_poly_poly_gquot).
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply pathsinv0l.
        }
        apply pathscomp0lid.
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          refine (!_).
          apply maponpaths_poly_gquot_gquot_poly.
        }
        apply pathsinv0l.
      }
      apply pathscomp0rid.
    }
    do 4 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply maponpathsidfun.
    }
    unfold gquot_endpoint_help_gcl.
    simpl.
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      do 3 apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply maponpathscomp.
        }
        do 2 apply maponpaths.
        apply pathscomp_inv.
      }
      etrans.
      {
        refine (!_).
        apply (maponpathscomp0
                 ((sem_endpoint_one_types (r j))
                    (gquot_functor_obj (pr1 G)
                     ,, prealg_gquot_map A (pr1 G) (pr2 G)))).
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply maponpathsinv0.
        }
        etrans.
        {
          apply maponpathscomp.
        }
        apply (maponpaths_homot gquot_poly_poly_gquot).
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          apply pathsinv0l.
        }
        etrans.
        {
          apply pathscomp0rid.
        }
        apply maponpathsidfun.
      }
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpathsinv0.
        }
        apply maponpaths.
        apply maponpaths_poly_gquot_gquot_poly.
      }
      apply pathsinv0l.
    }
    do 2 refine (path_assoc _ _ _ @ _).
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        apply pathscomp_inv.
      }
      apply maponpaths.
      refine (!_).
      apply maponpathsinv0.
    }
    do 2 refine (path_assoc _ _ _ @ _).
    apply idpath.
  - (* point constructor *)
    simpl.
    etrans.
    {
      apply maponpaths.
      exact IHp.
    }
    etrans.
    {
      apply (maponpathscomp0 (prealg_gquot_map A (pr1 G) (pr2 G))).
    }
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      apply (maponpathscomp0 (prealg_gquot_map A (pr1 G) (pr2 G))).
    }
    refine (!_).
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply pathscomp_inv.
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply maponpathsinv0.
    }
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    simpl.
    unfold prealg_gquot_map.
    simpl.
    refine (!_).
    etrans.
    {
      etrans.
      {
        exact (!(maponpathscomp
                   (poly_gquot A (pr1 G))
                   (gquot_functor_map (pr2 G))
                   _)).
      }
      apply maponpaths.
      etrans.
      {
        apply maponpathscomp.
      }
      apply (maponpaths_homot
               poly_gquot_gquot_poly).
    }
    etrans.
    {
      apply maponpathscomp0.
    }
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpathsinv0.
    }
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply maponpathsidfun.
    }
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - (* path argument *)
    simpl.
    unfold gquot_endpoint_help_gcl.
    unfold path_arg_to_mor.
    use path_rotate_rl.
    use path_inv_rotate_rr.
    refine (sem_homot_endpoint_one_types_sem_homot_endpoint_grpd_path_arg _ @ _).
    do 4 apply maponpaths.
    do 2 refine (!(path_assoc _ _ _) @ _).
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    apply path_assoc.
Qed.

Definition gquot_is_hit_algebra_lem
           {Σ : hit_signature}
           (X : hit_path_algebra_grpd Σ)
           (HX : is_hit_algebra_grpd Σ X)
           (i : homot_label Σ)
  : ∏ (z : gquot (poly_act_groupoid (homot_point_arg Σ i) (pr11 X)))
      (p : (sem_endpoint_one_types (homot_path_arg_left Σ i))
             ((total_prealg_gquot (point_constr Σ)) (pr1 X))
             (gquot_poly z)
           =
           (sem_endpoint_one_types (homot_path_arg_right Σ i))
             ((total_prealg_gquot (point_constr Σ)) (pr1 X))
             (gquot_poly z)),
    sem_homot_endpoint_one_types
      (homot_left_path Σ i)
      ((total_prealg_gquot (point_constr Σ)) (pr1 X))
      (λ j,
       (lift_gquot_add2cell (path_left Σ j) (path_right Σ j)) (pr1 X) (pr2 X j))
      (gquot_poly z)
      p
    =
    sem_homot_endpoint_one_types
      (homot_right_path Σ i)
      ((total_prealg_gquot (point_constr Σ)) (pr1 X))
      (λ j,
       (lift_gquot_add2cell (path_left Σ j) (path_right Σ j)) (pr1 X) (pr2 X j))
      (gquot_poly z)
      p.
Proof.
  use gquot_ind_prop.
  - intros a p.
    refine (sem_homot_endpoint_one_types_sem_homot_endpoint_grpd _ _ _ _ _
            @ _
            @ !(sem_homot_endpoint_one_types_sem_homot_endpoint_grpd _ _ _ _ _)).
    apply maponpaths.
    apply maponpaths_2.
    do 2 apply maponpaths.
    apply HX.
  - intro.
    use impred ; intro.
    exact (gtrunc _ _ _ _ _).
Qed.
    
Definition gquot_is_hit_algebra
           (Σ : hit_signature)
           (X : hit_path_algebra_grpd Σ)
  : is_hit_algebra_grpd Σ X
    →
    is_hit_algebra_one_types Σ (hit_path_algebra_gquot Σ X).
Proof.
  intros HX i z p.
  refine (sem_homot_endpoint_one_types_gquot_poly_poly_gquot _ _ _ _ _
          @ _
          @ !(sem_homot_endpoint_one_types_gquot_poly_poly_gquot _ _ _ _ _)).
  apply maponpaths.
  apply maponpaths_2.
  apply helpgquot_is_hit_algebra_lem.
  exact HX.
Qed.
