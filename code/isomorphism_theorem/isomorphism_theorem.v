(** The first isomorphism theorem for algebras *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.one_types_adjoint_equivalence.
Require Import displayed_algebras.globe_over_lem.
Require Import existence.initial_algebra.
Require Import isomorphism_theorem.congruence_relation.
Require Import isomorphism_theorem.congruence_mapping.
Require Import isomorphism_theorem.image.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Section FirstIsomorphismTheorem.
  Context {Σ : hit_signature}
          {X Y : hit_algebra_one_types Σ}
          (f : X --> Y).

  (**
     Step 1: we define a congruence relation on `X`
     We identitify `x` and `y` if `f x = f y`.
   *)
  Definition congruence_relation_groupoid_for_image
    : congruence_relation_groupoid X.
  Proof.
    use make_congruence_relation_groupoid.
    - exact (λ x y, alg_map_carrier f x = alg_map_carrier f y).
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - exact (λ _ _ _ p q, p @ q).
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
  Defined.

  Definition congruence_relation_ops_for_image
    : congruence_relation_ops X.
  Proof.
    use make_congruence_relation_ops.
    - exact congruence_relation_groupoid_for_image.
    - apply TODO.
    - apply TODO.
    - apply TODO.
  Defined.
  
  Definition congruence_relation_nat_for_image
    : congruence_relation_nat X.
  Proof.
    use make_congruence_relation_nat.
    - exact congruence_relation_ops_for_image.
    - apply TODO.
  Defined.
  
  Definition congruence_relation_for_image
    : congruence_relation X.
  Proof.
    use make_congruence_relation.
    - exact congruence_relation_nat_for_image.
    - apply TODO.
  Defined.

  (** Notation for the quotient *)
  Local Notation "'X/R'" := (quotient_of_congruence congruence_relation_for_image).
  
  (**
     Step 2: Define a map from the quotient to `im f`.
   *)
  Definition map_gquot_to_image
    : X/R --> image f.
  Proof.
    use factor_through_gquot.
    - exact (image_inj f).
    - simpl ; cbn.
      unfold image_inj_comp.
      intros a b p.
      use PathOverToTotalPath.
      + exact p.
      + apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
  Defined.

  (**
     Step 3: Show this map is a left adjoint equivalence
   *)
  Section FiberMapGQuot.
    Variable (x : alg_carrier X).

    Definition inverse_image_map_gquot
      : hfiber
          (alg_map_carrier map_gquot_to_image)
          (alg_map_carrier f x,, hinhpr (x,, idpath (alg_map_carrier f x)))
      := gcl (make_groupoid_algebra_carrier congruence_relation_for_image) x
         ,,
         idpath _.

    Definition inverse_image_map_gquot_all_path_base
      : ∏ (z : alg_carrier X/R),
        alg_map_carrier
          map_gquot_to_image
          z
        =
        alg_map_carrier f x
        ,,
        hinhpr (x,, idpath (alg_map_carrier f x))
        →
        z
        =
        gcl (make_groupoid_algebra_carrier congruence_relation_for_image) x.
    Proof.
      use gquot_ind_set ; simpl.
      - exact (λ a p,
               gcleq
                 (make_groupoid_algebra_carrier congruence_relation_groupoid_for_image)
                 (maponpaths pr1 p)).
      - abstract
          (simpl ;
           intros a₁ a₂ g ;
           apply PathOver_arrow ;
           intro p ;
           apply map_PathOver ;
           unfold square ;
           rewrite maponpathsidfun ;
           rewrite maponpaths_for_constant_function ;
           rewrite pathscomp0rid ;
           refine (!(gconcat _ _ _) @ _) ;
           apply maponpaths ;
           unfold transportb ;
           rewrite transportf_paths_FlFr ;
           rewrite maponpaths_for_constant_function ;
           rewrite pathscomp0rid ;
           rewrite maponpathsinv0 ;
           rewrite pathsinv0inv0 ;
           rewrite maponpathscomp0 ;
           refine (!_) ;
           apply maponpaths_2 ;
           refine (maponpaths
                     (maponpaths pr1)
                     (factor_through_gquot_gcleq
                        congruence_relation_for_image
                        (image f)
                        _ _ _ _ _ _
                        g)
                   @ _) ;
           apply maponpaths_pr1_PathOverToTotalPath).
      - intro.
        use funspace_isaset.
        exact (gtrunc _ _ _).
    Defined.

    Definition inverse_image_map_gquot_all_path_fib
      : ∏ (z : alg_carrier X/R)
          (p : alg_map_carrier map_gquot_to_image z
               =
               alg_map_carrier f x,, hinhpr (x,, idpath (alg_map_carrier f x))),
        maponpaths
          (alg_map_carrier map_gquot_to_image)
          (inverse_image_map_gquot_all_path_base z p)
        =
        p.
    Proof.
      use gquot_ind_prop.
      - intros a p.
        simpl.
        etrans.
        {
          exact (factor_through_gquot_gcleq
                   congruence_relation_for_image
                   (image f)
                   _ _ _ _ _ _
                   _).
        }
        refine (_ @ !(PathOverToTotalPath'_eta _)).
        unfold PathOverToTotalPath'.
        use globe_over_to_homot.
        * apply idpath.
        * use path_globe_over_hset.
          intro.
          apply isasetaprop.
          simpl.
          exact (pr2 (ishinh _)).
      - intro ; simpl.
        use impred_isaprop ; intro ; simpl.
        exact (one_type_isofhlevel _ _ _ _ _).
    Qed.
        
    Definition inverse_image_map_gquot_all_path
               (t : hfiber
                      (alg_map_carrier map_gquot_to_image)
                      (alg_map_carrier f x,, hinhpr (x,, idpath (alg_map_carrier f x))))
      : t = inverse_image_map_gquot.
    Proof.
      induction t as [z p].
      use PathOverToTotalPath.
      - exact (inverse_image_map_gquot_all_path_base z p).
      - abstract
          (use map_PathOver ;
           unfold square ;
           refine (pathscomp0rid _ @ _) ;
           refine (!_) ;
           refine (maponpaths (λ z, _ @ z) (maponpaths_for_constant_function _ _) @ _) ;
           refine (pathscomp0rid _ @ _) ;
           refine (!_) ;
           exact (inverse_image_map_gquot_all_path_fib z p)).
    Qed.
  End FiberMapGQuot.
  
  Definition map_gquot_to_image_is_adjequiv
    : left_adjoint_equivalence map_gquot_to_image.
  Proof.
    use isweq_to_hit_algebra_adjequiv.
    intro y.
    induction y as [y p].
    simpl in p.
    revert p.
    use (squash_rec
           (λ p, make_hProp
                   (iscontr (hfiber (alg_map_carrier map_gquot_to_image) (y,, p)))
                   _)).
    - apply isapropiscontr.
    - intro x ; simpl.
      induction x as [x p].
      induction p ; simpl.
      use make_iscontr.
      + exact (inverse_image_map_gquot x).
      + exact (inverse_image_map_gquot_all_path x).
  Defined.
End FirstIsomorphismTheorem.
