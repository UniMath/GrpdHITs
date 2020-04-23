(**
Adjoint equivalences in the bicategory of algebras.
Note that we do not use the displayed machinery here.
That is because the given displayed machinery treats the displayed adjoint for arbitrary bicategories.
However, for 1-types, we can simplify these formulas, which is done in this file.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import existence.initial_algebra.

Local Open Scope cat.

Definition unit_lemma
           {P : poly_code}
           {X Y : UU}
           {L : X → Y} {R : Y → X}
           (η : ∏ (x : X), x = R(L x))
           (ε : ∏ (y : Y), L(R y) = y)
           (t : ∏ (x : X), maponpaths L (η x) = !(ε(L x)))
           (x : poly_act P X)
  : maponpaths
      (poly_map P L)
      (poly_id P X x
    @ poly_homot P η x
    @ !(poly_comp P L R x))
    =
    poly_id P Y (poly_map P L x)
    @ poly_homot P (invhomot ε) (poly_map P L x)
    @ !(poly_comp P R L (poly_map P L x)).
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - simpl.
    etrans.
    {
      apply maponpaths.
      apply pathscomp0rid.
    }
    refine (_ @ !(pathscomp0rid _)).
    exact (t x).
  - induction x as [x | x].
    + simpl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 inl _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      refine (maponpathscomp inl (coprodf _ _) _ @ _).
      refine (!(maponpathscomp _ inl _) @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 inl _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      apply maponpaths.
      exact (!(IHP₁ x)).
    + simpl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 inr _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      refine (maponpathscomp inr (coprodf _ _) _ @ _).
      refine (!(maponpathscomp _ inr _) @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 inr _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      apply maponpaths.
      exact (!(IHP₂ x)).
  - simpl.
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
            apply pathsdirprod_inv.
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
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
    exact (!(paths_pathsdirprod (IHP₁ _) (IHP₂ _))).
Qed.        

Section HITAlgebraAdjEquiv.
  Context {Σ : hit_signature}
          {X Y : hit_algebra_one_types Σ}
          (f : X --> Y)
          (Hf : @left_adjoint_equivalence one_types _ _ (alg_map_carrier f)).

  Local Notation "'L'" := (alg_map_carrier f).
  Local Notation "'R'" := (left_adjoint_right_adjoint Hf : alg_carrier Y → alg_carrier X).
  Local Notation "'η'" := (left_adjoint_unit Hf).
  Local Notation "'ε'" := (left_adjoint_counit Hf).

  Local Definition R_preserves_point
    : preserves_point R.
  Proof.
    intro x.
    refine (maponpaths
              (λ z, R(prealg_constr z))
              (poly_id (point_constr Σ) _ x
               @ poly_homot _ (invhomot ε) x
               @ !(poly_comp _ R L x))
            @ _).
    refine (maponpaths R (!(alg_map_commute f _)) @ _).
    exact (!η (prealg_constr (poly_map (point_constr Σ) R x))).
  Defined.

  Local Definition hit_algebra_is_adjequiv_prealg_right_adjoint
    : pr11 Y --> pr11 X.
  Proof.
    use make_hit_prealgebra_mor.
    - exact R.
    - exact R_preserves_point.
  Defined.

  Local Definition poly_lem
        (P : poly_code)
        (x : poly_act P (alg_carrier Y))
    : poly_comp P R L x
      @ poly_homot P ε x
      @ !(poly_id P _ x)
      @ poly_id P _ x
      @ poly_homot P (invhomot ε) x
      @ !(poly_comp P R L x)
      =
      idpath _.
  Proof.
    etrans.
    {
      do 2 apply maponpaths.
      do 2 refine (path_assoc _ _ _ @ _).
      do 2 apply maponpaths_2.
      apply pathsinv0l.
    }
    cbn.
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply poly_homot_inv.
      }
      apply pathsinv0r.
    }
    cbn.
    apply pathsinv0r.
  Qed.

  Local Definition LR_triangle
        (x : alg_carrier X)
    : maponpaths L (η x)
      =
      !(ε (L x)).
  Proof.
    pose (eqtohomot
            (pr1 (axioms_of_left_adjoint Hf))
            x)
      as H.
    cbn in H.
    unfold homotcomp, homotfun, funhomotsec, homotrefl in H.
    cbn in H.
    rewrite !pathscomp0rid in H.
    refine (_ @ pathscomp0lid _).
    use path_inv_rotate_rr.
    exact H.
  Qed.    

  Local Definition sem_endpoint_UU_natural_for_R
        {P Q : poly_code}
        (e : endpoint (point_constr Σ) P Q)
        (x : poly_act P (alg_carrier Y))
    : maponpaths
        (poly_map Q L)
        (sem_endpoint_UU_natural e R_preserves_point x)
      =
      poly_comp _ _ _ _
      @ poly_homot Q ε _
      @ !(poly_id _ _ _)
      @ maponpaths
          (sem_endpoint_UU e prealg_constr)
          (poly_id _ _ _
           @ poly_homot _ (invhomot ε) _
           @ !(poly_comp _ _ _ _))
      @ !(sem_endpoint_UU_natural
            e
            (alg_map_commute f)
            (poly_map P R x)).
  Proof.
    induction e as [P | P Q S e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q S e₁ IHe₁ e₂ IHe₂
                    | P T t | C₁ C₂ g | ].
    - simpl.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        refine (pathscomp0rid _ @ _).
        apply maponpathsidfun.
      }
      apply poly_lem.
    - simpl.
      etrans.
      {
        refine (maponpathscomp0 _ _ _ @ _).
        apply maponpaths_2.
        apply IHe₂.
      }
      clear IHe₂.
      do 3 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply pathscomp_inv.
      }
      refine (!_).
      etrans.
      {
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply maponpathscomp.
        }
        refine (!_).
        apply (homotsec_natural'
                 (invhomot (sem_endpoint_UU_natural e₂ (alg_map_commute f)))).
      }
      unfold invhomot.
      refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (maponpathscomp (poly_map Q L) (sem_endpoint_UU e₂ prealg_constr)).
        }
        refine (!_).
        apply maponpathscomp0.
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathsinv0 _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply maponpathscomp.
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply IHe₁.
      }
      clear IHe₁.
      do 3 refine ((path_assoc _ _ _) @ _).
      refine (_ @ pathscomp0lid _).
      apply maponpaths_2.
      do 3 refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        do 2 refine (path_assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        apply pathsinv0l.
      }
      cbn.
      etrans.
      {
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply poly_homot_inv.
        }
        apply pathsinv0l.
      }
      cbn.
      apply pathsinv0r.
    - simpl.
      refine (!_).
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
              apply pathscomp0rid.
            }
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply maponpathsinv0.
            }
            exact (!(maponpathscomp0 _ _ _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      refine (_ @ maponpaths_idpath).
      apply maponpaths.
      apply poly_lem.
    - simpl.
      refine (!_).
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
              apply pathscomp0rid.
            }
            etrans.
            {
              apply maponpaths_2.
              refine (!_).
              apply maponpathsinv0.
            }
            exact (!(maponpathscomp0 _ _ _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      refine (_ @ maponpaths_idpath).
      apply maponpaths.
      apply poly_lem.
    - simpl.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        refine (pathscomp0rid _ @ _).
        etrans.
        {
          apply maponpaths.
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
        apply maponpaths_pr1_pathsdirprod.
      }
      apply poly_lem.
    - simpl.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        refine (pathscomp0rid _ @ _).
        etrans.
        {
          apply maponpaths.
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
        apply maponpaths_pr2_pathsdirprod.
      }
      apply poly_lem.
    - simpl.
      refine (!(maponpaths_pathsdirprod _ _ _ _) @ _).
      refine (!_).
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
              etrans.
              {
                apply maponpaths.
                apply pathsdirprod_inv.
              }
              etrans.
              {
                apply maponpaths_2.
                apply maponpaths_prod_path.
              }
              apply pathsdirprod_concat.
            }
            etrans.
            {
              apply maponpaths_2.
              apply pathsdirprod_inv.
            }
            apply pathsdirprod_concat.
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      refine (!_).
      exact (paths_pathsdirprod (IHe₁ _) (IHe₂ _)).
    - simpl.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      apply maponpaths_for_constant_function.
    - apply idpath.
    - simpl.
      unfold R_preserves_point.
      etrans.
      {
        apply maponpaths.
        apply path_assoc.
      }
      refine (maponpathscomp0 _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply maponpathscomp.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        apply maponpathscomp.
      }
      etrans.
      {
        apply maponpaths.
        refine (maponpathsinv0 _ _ @ _).
        apply maponpaths.
        apply LR_triangle.
      }
      cbn.
      etrans.
      {
        apply maponpaths.
        apply pathsinv0inv0.
      }
      refine (maponpaths_homotsec ε _ @ _).
      apply maponpaths.
      apply maponpathsidfun.
  Qed.

  Local Definition hit_algebra_is_adjequiv_right_adjoint_preserves_path_help
        (i : path_label Σ)
        (x : poly_act (path_source Σ i) (alg_carrier Y))
    : maponpaths
        L
        (maponpaths R (alg_path Y i x)
         @ sem_endpoint_UU_natural (path_right Σ i) R_preserves_point x)
      =
      maponpaths
        L
        (sem_endpoint_UU_natural (path_left Σ i) R_preserves_point x
         @ alg_path X i (poly_map (path_source Σ i) R x)).
  Proof.
    pose (maponpaths_homotsec ε (alg_path Y i x)) as p.
    rewrite maponpathsidfun in p.
    pose (alg_map_path f i (poly_map _ R x)) as q.
    cbn in q.
    etrans.
    {
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths_2.
      apply maponpathscomp.
    }
    etrans.
    {
      apply maponpaths.
      exact (sem_endpoint_UU_natural_for_R (path_right Σ i) x).
    }
    rewrite !path_assoc.
    use path_inv_rotate_lr.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (sem_endpoint_UU_natural_for_R (path_left Σ i) x).
    }
    refine (!_).
    simpl.
    rewrite !pathscomp0rid.
    etrans.
    {
      apply maponpaths_2.
      exact p.
    }
    rewrite <- !path_assoc.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      exact q.
    }
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0l.
    }
    simpl.
    apply (homotsec_natural' (alg_path Y i)).
  Qed.
      
  Local Definition hit_algebra_is_adjequiv_right_adjoint_preserves_path
    : preserves_path
        _
        (prealg_map_commute hit_algebra_is_adjequiv_prealg_right_adjoint).
  Proof.
    intros i x.
    pose (hit_algebra_is_adjequiv_right_adjoint_preserves_path_help i x).
    exact (invmaponpathsincl
             (maponpaths L)
             (isinclweq
                _ _ _
                (isweqmaponpaths
                   (make_weq L (adjoint_equivalence_is_weq _ Hf))
                   _ _))
             _ _
             p).
  Qed.

  Local Definition hit_algebra_is_adjequiv_right_adjoint
    : Y --> X.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - exact hit_algebra_is_adjequiv_prealg_right_adjoint.
    - exact hit_algebra_is_adjequiv_right_adjoint_preserves_path.
  Defined.
  
  Local Definition hit_algebra_is_adjequiv_unit_is_algebra_2cell
    : @is_algebra_2cell
        _ _ _
        (id₁ X) (f · hit_algebra_is_adjequiv_right_adjoint)
        η.
  Proof.
    intro x.
    cbn ; unfold homotcomp, homotfun, funhomotsec ; cbn.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (pathscomp0rid _ @ _).
      apply maponpaths_2.
      apply pathscomp0rid.
    }
    unfold R_preserves_point.
    refine (path_assoc _ _ _ @ _).
    refine (!_).
    refine (!(maponpathscomp0 _ _ _) @ _).
    refine (!(pathscomp0rid _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (!(pathsinv0l
                 (maponpaths
                    (alg_constr X)
                    (poly_comp _ _ _ _)))).
    }
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathsinv0 _ _)).
    }
    refine (!(maponpathscomp0 _ _ _) @ _).
    do 3 refine (_ @ !(path_assoc _ _ _)).
    use path_inv_rotate_rr.
    refine (!_).
    do 2 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply maponpathscomp.
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      exact (!(maponpathscomp0 _ _ _)).
    }
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathsidfun _)).
      }
      apply (homotsec_natural' η).
    }
    apply maponpaths.
    refine (!(maponpathscomp L R _) @ _).
    apply maponpaths.
    refine (_ @ !(path_assoc _ _ _)).
    use path_inv_rotate_rr.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp.
      }
      apply (homotsec_natural' (alg_map_commute f)).
    }
    apply maponpaths.
    refine (!(maponpathscomp _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      exact (!(path_assoc _ _ _)).
    }
    refine (unit_lemma
              _
              _
              _
              x).
    apply LR_triangle.
  Qed.

  Local Definition hit_algebra_is_adjequiv_unit
    : id₁ X ==> f · hit_algebra_is_adjequiv_right_adjoint.
  Proof.
    use make_algebra_2cell.
    - exact η.
    - exact hit_algebra_is_adjequiv_unit_is_algebra_2cell.
  Defined.

  Local Definition hit_algebra_is_adjequiv_counit_is_algebra_2cell
    : @is_algebra_2cell
        _ _ _
        (hit_algebra_is_adjequiv_right_adjoint · f) (id₁ Y)
        ε.
  Proof.
    intro x.
    cbn ; unfold homotcomp, homotfun, funhomotsec ; cbn.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (pathscomp0rid _ @ _).
      apply maponpaths_2.
      apply pathscomp0rid.
    }
    unfold R_preserves_point.
    do 2 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      apply maponpaths.
      exact (!(maponpathscomp0 (alg_constr Y) _ _)).
    }


    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply path_assoc.
      }
      etrans.
      {        
        apply maponpathscomp0.
      }
      apply maponpaths.
      refine (maponpathsinv0 _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply LR_triangle.
      }
      apply pathsinv0inv0.
    }
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            exact (!(maponpathscomp _ R _)).
          }
          exact (!(maponpathscomp0 R _ _)).
        }
        apply (maponpathscomp R L).
      }
      apply (homotsec_natural' ε).
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply maponpathsidfun.
    }
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0l.
    }
    cbn.
    refine (!(maponpathscomp0 (alg_constr Y) _ _) @ _).
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0l.
    }
    simpl.
    refine (_ @ pathscomp0rid _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply poly_homot_inv.
    }
    apply pathsinv0l.
  Qed.

  Local Definition hit_algebra_is_adjequiv_counit
    : hit_algebra_is_adjequiv_right_adjoint · f ==> id₁ Y.
  Proof.
    use make_algebra_2cell.
    - exact ε.
    - exact hit_algebra_is_adjequiv_counit_is_algebra_2cell.
  Defined.
  
  Local Definition hit_algebra_is_adjequiv_data
    : left_adjoint_data f.
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - exact hit_algebra_is_adjequiv_right_adjoint.
    - exact hit_algebra_is_adjequiv_unit.
    - exact hit_algebra_is_adjequiv_counit.
  Defined.

  Local Definition hit_algebra_is_adjequiv_adjoint_axioms
    : left_adjoint_axioms hit_algebra_is_adjequiv_data.
  Proof.
    split.
    - use algebra_2cell_eq.
      exact (eqtohomot (pr1 (axioms_of_left_adjoint Hf))).
    - use algebra_2cell_eq.
      exact (eqtohomot (pr2 (axioms_of_left_adjoint Hf))).
  Qed.

  Local Definition hit_algebra_is_adjequiv_equivalence_axioms
    : left_equivalence_axioms hit_algebra_is_adjequiv_data.
  Proof.
    split ; apply hit_alg_is_invertible_2cell_one_type.
  Qed.

  Definition hit_algebra_is_adjequiv
    : left_adjoint_equivalence f.
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - exact hit_algebra_is_adjequiv_data.
    - exact hit_algebra_is_adjequiv_adjoint_axioms.
    - exact hit_algebra_is_adjequiv_equivalence_axioms.
  Qed.
End HITAlgebraAdjEquiv.

Definition isweq_to_hit_algebra_adjequiv
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           (f : X --> Y)
           (Hf : isweq (alg_map_carrier f))
  : left_adjoint_equivalence f.
Proof.
  use hit_algebra_is_adjequiv.
  exact (adjequiv_to_weq _ _ (make_weq _ Hf)).
Defined.
