(**
Biadjunction when adding a 2-cell to the algebra structure
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

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
Require Import biadjunctions.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import hit_biadjunction.gquot_natural.
Require Import hit_biadjunction.hit_prealgebra_biadj.

Local Definition TODO {A : UU} : A.
Admitted.

Local Open Scope cat.

Local Arguments nat_trans_comp {_ _ _ _ _} _ _.

(** Lemmata *)
Definition poly_path_groupoid_is_id
           {P : poly_code}
           {X : one_type}
           (z : poly_act P X)
  : pr1 (poly_path_groupoid P X) z = z.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (idpath z).
  - exact (idpath z).
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
Defined.

Definition poly_act_groupoid_to_path
           {P : poly_code}
           {X : one_type}
           {x y : poly_act P (one_type_to_groupoid X)}
           (p : poly_act_morphism P (one_type_to_groupoid X) x y)
  : x = y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact p.
  - exact p.
  - induction x as [x | x], y as [y | y].
    + exact (maponpaths inl (IHP₁ _ _ p)).
    + exact (fromempty p).
    + exact (fromempty p).
    + exact (maponpaths inr (IHP₂ _ _ p)).
  - exact (pathsdirprod (IHP₁ _ _ (pr1 p)) (IHP₂ _ _ (pr2 p))).
Defined.

Definition path_groupoid_endpoint
           {A S T : poly_code}
           (e : endpoint A S T)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (z : poly_act S (pr1 X : one_type))
  : pr1
      ((sem_endpoint_grpd e)
         (one_type_to_groupoid
            (pr1 X),,
            (poly_path_groupoid A) (pr1 X) ∙ function_to_functor (pr2 X))) z
    =
    (sem_endpoint_one_types e) X z.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ].
  - (* Identity *)
    exact (idpath z).
  - (* Composition *)
    exact (maponpaths (λ z, pr1 (sem_endpoint_grpd e₂ _) z) (IHe₁ z) @ IHe₂ _).
  - (* Left inclusion *)
    exact (idpath _).
  - (* Right inclusion *)
    exact (idpath _).
  - (* Left projection *)
    exact (idpath _).
  - (* Right projection *)
    exact (idpath _).
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ z) (IHe₂ z)).
  - (* Constant *)
    exact (idpath _).
  - (* Constant map *)
    exact (idpath _).
  - (* Constructor *)
    exact (maponpaths (pr2 X) (poly_path_groupoid_is_id z)).
Defined.

Definition poly_path_groupoid_is_id_is_nat
           {P : poly_code}
           {X : one_type}
           {x y : poly_act P X}
           (f : poly_act_morphism P (one_type_to_groupoid X) x y)
  : # ((poly_path_groupoid P) X : _ ⟶ _) f
    =
    maponpaths
      (λ z, (pr1 ((poly_path_groupoid P) X)) z)
      (poly_act_groupoid_to_path f).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (!(maponpathsidfun _)).
  - exact (!(maponpathsidfun _)).
  - induction x as [x | x], y as [y | y].
    + refine (maponpaths (maponpaths inl) (IHP₁ _ _ f) @ _).
      refine (maponpathscomp _ _ _ @ _).
      exact (!(maponpathscomp inl _ _)).
    + exact (fromempty f).
    + exact (fromempty f).
    + refine (maponpaths (maponpaths inr) (IHP₂ _ _ f) @ _).
      refine (maponpathscomp _ _ _ @ _).
      exact (!(maponpathscomp inr _ _)).
  - refine (maponpaths (λ z, pathsdirprod z _) (IHP₁ _ _ (pr1 f))
             @ maponpaths (pathsdirprod _) (IHP₂ _ _ (pr2 f))
             @ _).
    apply maponpaths_pathsdirprod.
Qed.

Definition path_groupoid_endpoint_is_nat
           {A S T : poly_code}
           (e : endpoint A S T)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           {z₁ z₂ : poly_act S (pr1 X : one_type)}
           (f : poly_act_morphism S (one_type_to_groupoid (pr1 X)) z₁ z₂)
  : poly_act_groupoid_to_path
      (#(pr1(pr111
               (sem_endpoint_grpd e)
               (one_type_to_groupoid
                  (pr1 X),,
                  (poly_path_groupoid A) (pr1 X) ∙ function_to_functor (pr2 X))))
        f)
      @ path_groupoid_endpoint e z₂
    =
    (path_groupoid_endpoint e z₁)
      @ maponpaths ((sem_endpoint_one_types e) X) (poly_act_groupoid_to_path f).
Proof.
  refine (_ @ homotsec_natural'
                (λ (z : poly_act S (pr1 X : one_type)), path_groupoid_endpoint e z)
                _).
  apply maponpaths_2.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - (* Identity *)
    exact (!(maponpathsidfun _)).
  - (* Composition *)
    simpl ; cbn.
    refine (!_).
    refine (!(maponpathscomp _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (!(IHe₁ _ _ _)).
    }
    refine (!_).
    apply IHe₂.
  - (* Left inclusion *)
    apply idpath.
  - (* Right inclusion *)
    apply idpath.
  - (* Left projection *)
    exact (!(maponpaths_pr1_pathsdirprod _ _)).
  - (* Right projection *)
    exact (!(maponpaths_pr2_pathsdirprod _ _)).
  - (* Pairing *)
    simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths_pair.
    }
    refine (!_).
    refine (maponpaths (λ z, pathsdirprod z _) (IHe₁ _ _ f) @ _).
    exact (maponpaths (pathsdirprod _) (IHe₂ _ _ f)).
  - (* Constant *)
    exact (!(maponpaths_for_constant_function _ _)).
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    simpl.
    refine (_ @ maponpathscomp (λ z, pr1 (poly_path_groupoid A (pr1 X)) z) (pr2 X) _).
    apply maponpaths.
    apply poly_path_groupoid_is_id_is_nat.
Qed.

Definition poly_act_morphism_path_groupoid
           {P : poly_code}
           {X : one_type}
           {x y : poly_act P (one_type_to_groupoid X)}
  : poly_act_morphism P (one_type_to_groupoid X) x y → x = y.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ p, p).
  - exact (λ p, p).
  - induction x as [x | x], y as [y | y].
    + exact (λ p, maponpaths inl (IHP₁ x y p)).
    + exact fromempty.
    + exact fromempty.
    + exact (λ p, maponpaths inr (IHP₂ x y p)).
  - exact (λ p, pathsdirprod (IHP₁ _ _ (pr1 p)) (IHP₂ _ _ (pr2 p))).
Defined.

Definition poly_act_morphism_path_groupoid_poly_act_identity
           (P : poly_code)
           {X Y : one_type}
           (f : X → Y)
           (z : poly_act P X)
  : poly_act_morphism_path_groupoid
       (poly_act_identity P (one_type_to_groupoid Y) (poly_map P f z))
     =
     idpath _.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + exact (maponpaths (maponpaths inl) (IHP₁ z)).
    + exact (maponpaths (maponpaths inr) (IHP₂ z)).
  - exact (maponpaths
             (λ z, pathsdirprod z _)
             (IHP₁ (pr1 z))
           @ maponpaths
               (pathsdirprod _)
               (IHP₂ (pr2 z))).
Qed.

Definition map_on_sem_endpoint_one_types_natural_constr_help
           {P : poly_code}
           {X Y : one_type}
           (f : X → Y)
           (z : poly_act P X)
  : maponpaths
      (poly_map P f)
      (poly_path_groupoid_is_id z)
    =
    (pr11 (psnaturality_of (poly_path_groupoid P) f)) z
    @ poly_path_groupoid_is_id (poly_map P f z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + refine (_ @ maponpathscomp0
                    inl
                    ((pr11 (psnaturality_of (poly_path_groupoid P₁) f)) z)
                    (poly_path_groupoid_is_id (poly_map P₁ f z))).
      refine (coprodf_path_maponpaths_inl
                (poly_map P₁ f) (poly_map P₂ f)
                (poly_path_groupoid_is_id z)
              @ _).
      exact (maponpaths (maponpaths inl) (IHP₁ z)).
    + refine (_ @ maponpathscomp0
                    inr
                    ((pr11 (psnaturality_of (poly_path_groupoid P₂) f)) z)
                    (poly_path_groupoid_is_id (poly_map P₂ f z))).
      refine (coprodf_path_maponpaths_inr
                (poly_map P₁ f) (poly_map P₂ f)
                (poly_path_groupoid_is_id z)
              @ _).
      exact (maponpaths (maponpaths inr) (IHP₂ z)).
  - refine (_ @ !(pathsdirprod_concat
                    ((pr11 (psnaturality_of (poly_path_groupoid P₁) f)) (pr1 z))
                    (poly_path_groupoid_is_id (poly_map P₁ f (pr1 z)))
                    ((pr11 (psnaturality_of (poly_path_groupoid P₂) f)) (pr2 z))
                    (poly_path_groupoid_is_id (poly_map P₂ f (pr2 z))))).
    refine (!(maponpaths_pathsdirprod
                (poly_map P₁ f) (poly_map P₂ f)
                (poly_path_groupoid_is_id (pr1 z)) (poly_path_groupoid_is_id (pr2 z)))
             @ _).
    exact (maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
           @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
Qed.
      
Definition map_on_sem_endpoint_one_types_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (f : X --> Y)
           (z : poly_act P (pr1 X : one_type))
  : poly_act_morphism_path_groupoid
      ((pr11 (psnaturality_of
                (sem_endpoint_grpd e)
                (# (total_prealg_path_groupoid A) f))) z)
  @ path_groupoid_endpoint e (poly_map P (pr1 f) z)
  =
  maponpaths (poly_map Q (pr1 f)) (path_groupoid_endpoint e z)
  @ pr1 (psnaturality_of (sem_endpoint_one_types e) f) z.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - (* Identity *)
    refine (pathscomp0rid _ @ _).
    refine (_ @ poly_act_morphism_path_groupoid_poly_act_identity P (pr1 f) z).

    apply maponpaths.
    exact (poly_act_id_left
             P
             (one_type_to_groupoid (pr1 Y))
             (poly_map P (pr1 f) z)
             (poly_map P (pr1 f) z)
             (poly_act_identity
                P (one_type_to_groupoid (pr1 Y))
                (poly_map P (pr1 f) z))             
          ).
  - (* Composition *)
    specialize (IHe₁ z).
    specialize (IHe₂ (sem_endpoint_one_types e₁ X z)).
    apply TODO.
  - (* Left inclusion *)
    refine (pathscomp0rid _ @ _).
    exact (maponpaths
             (maponpaths inl)
             (poly_act_morphism_path_groupoid_poly_act_identity P _ _)).
  - (* Right inclusion *)
    refine (pathscomp0rid _ @ _).
    exact (maponpaths
             (maponpaths inr)
             (poly_act_morphism_path_groupoid_poly_act_identity Q _ _)).
  - (* Left projection *)
    refine (pathscomp0rid _ @ _).
    exact (poly_act_morphism_path_groupoid_poly_act_identity P _ _).
  - (* Right projection *)
    refine (pathscomp0rid _ @ _).
    exact (poly_act_morphism_path_groupoid_poly_act_identity Q _ _).
  - (* Pairing *)
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (maponpaths_pathsdirprod
               (poly_map Q (pr1 f)) (poly_map R (pr1 f))
               (path_groupoid_endpoint e₁ z) (path_groupoid_endpoint e₂ z)).
    }
    refine (pathsdirprod_concat
              (maponpaths (poly_map Q (pr1 f)) (path_groupoid_endpoint e₁ z))
              (pr1 (psnaturality_of (sem_endpoint_one_types e₁) f) z)
              (maponpaths (poly_map R (pr1 f)) (path_groupoid_endpoint e₂ z))
              (pr1 (psnaturality_of (sem_endpoint_one_types e₂) f) z)
            @ _).
    refine (!_).
    refine (pathsdirprod_concat
              (poly_act_morphism_path_groupoid
                 ((pr11 (psnaturality_of
                           (sem_endpoint_grpd e₁)
                           (# (total_prealg_path_groupoid A) f))) z))
              (path_groupoid_endpoint e₁ (poly_map P (pr1 f) z))
              (poly_act_morphism_path_groupoid
                 ((pr11 (psnaturality_of
                           (sem_endpoint_grpd e₂)
                           (# (total_prealg_path_groupoid A) f))) z))
              (path_groupoid_endpoint e₂ (poly_map P (pr1 f) z))
              @ _).
    refine (maponpaths (λ z, pathsdirprod z _) (IHe₁ z) @ _).
    exact (maponpaths (pathsdirprod _) (IHe₂ z)).
  - (* Constant *)
    apply idpath.
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (maponpathscomp (pr2 X) (pr1 f)).
    }
    refine (homotsec_natural' (pr12 f) (poly_path_groupoid_is_id z) @ _).
    apply maponpaths.
    refine (!(maponpathscomp (poly_map A (pr1 f)) (pr2 Y) _) @ _).
    refine (_ @ maponpathscomp0 (pr2 Y) _ _).
    apply maponpaths.
    exact (map_on_sem_endpoint_one_types_natural_constr_help (pr1 f) z).
Time Qed.

Definition map_on_sem_endpoint_one_types_natural'
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (f : X --> Y)
           (z : poly_act P (pr1 X : one_type))
  : maponpaths (poly_map Q (pr1 f)) (! path_groupoid_endpoint e z)
  @ poly_act_morphism_path_groupoid
      ((pr11 (psnaturality_of
                (sem_endpoint_grpd e)
                (# (total_prealg_path_groupoid A) f))) z)
  =
  pr1 (psnaturality_of (sem_endpoint_one_types e) f) z
  @ ! path_groupoid_endpoint e (poly_map P (pr1 f) z).
Proof.
  use path_inv_rotate_rr.
  refine (!(path_assoc _ _ _) @ _).
  etrans.
  {
    apply maponpaths_2.
    apply maponpathsinv0.
  }
  use path_inv_rotate_ll.
  exact (map_on_sem_endpoint_one_types_natural e f z).
Qed.
  
Section LiftPathGroupoid.
  Context {A S : poly_code}
          (l r : endpoint A S I).

  Definition path_alg_path_groupoid_ob_comp
             {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             (p : homotsec ((sem_endpoint_one_types l) X) ((sem_endpoint_one_types r) X))
    : nat_trans_data
        (pr1
           ((sem_endpoint_grpd l)
              (one_type_to_groupoid (pr1 X),,
               prealg_path_groupoid_map A (pr1 X) (pr2 X))))
        (pr1
           ((sem_endpoint_grpd r)
              (one_type_to_groupoid (pr1 X),,
               prealg_path_groupoid_map A (pr1 X) (pr2 X))))
    := λ z, path_groupoid_endpoint l z @ p z @ !(path_groupoid_endpoint r z).

  Definition path_alg_path_groupoid_ob_is_nat_trans
             {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             (p : sem_endpoint_one_types l X ~ sem_endpoint_one_types r X)
    : is_nat_trans _ _ (path_alg_path_groupoid_ob_comp p).
  Proof.
    intros z₁ z₂ f ; cbn.
    unfold path_alg_path_groupoid_ob_comp.
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (path_groupoid_endpoint_is_nat l f).
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (PathOver_to_square (apd p (poly_act_groupoid_to_path f))).
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    apply path_inv_rotate_lr.
    refine (_ @ path_assoc _ _ _).
    refine (!_).
    apply path_inv_rotate_ll.
    exact (path_groupoid_endpoint_is_nat r f).
  Qed.
  
  Definition path_alg_path_groupoid_ob
             {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             (p : homotsec ((sem_endpoint_one_types l) X) ((sem_endpoint_one_types r) X))
    : pr1
        ((sem_endpoint_grpd l)
           (one_type_to_groupoid (pr1 X),,
            prealg_path_groupoid_map A (pr1 X) (pr2 X)))
    ⟹
    pr1
    ((sem_endpoint_grpd r)
       (one_type_to_groupoid (pr1 X),,
        prealg_path_groupoid_map A (pr1 X) (pr2 X))).
  Proof.
    use make_nat_trans.
    - exact (path_alg_path_groupoid_ob_comp p).
    - exact (path_alg_path_groupoid_ob_is_nat_trans p).
  Defined.
  
  Local Notation "'D'" := (add_cell_disp_cat
                              (disp_alg_bicat (⟦ A ⟧))
                              (⟦ S ⟧)
                              (⟦ I ⟧)
                              (sem_endpoint_one_types l)
                              (sem_endpoint_one_types r)).

  Definition path_alg_path_groupoid_mor_equation
             {X Y : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             {f : X --> Y}
             {hX : sem_endpoint_one_types l X ~ sem_endpoint_one_types r X}
             {hY : sem_endpoint_one_types l Y ~ sem_endpoint_one_types r Y}
             (hf : @mor_disp _ D X Y hX hY f)
             (z : poly_act S (pr1 X : one_type))
    : maponpaths (pr1 f) (path_alg_path_groupoid_ob_comp hX z)
    @ (pr11
         (psnaturality_of
            (sem_endpoint_grpd r)
            (# (total_prealg_path_groupoid A) f))
         z)
    =
    (pr11
       (psnaturality_of
          (sem_endpoint_grpd l)
          (# (total_prealg_path_groupoid A) f))
       z)
    @ path_alg_path_groupoid_ob_comp hY (poly_map S (pr1 f) z).
  Proof.
    unfold path_alg_path_groupoid_ob_comp.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          exact (path_assoc _ _ _).
        }
        apply maponpathscomp0.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      exact (map_on_sem_endpoint_one_types_natural' r f z).
    }
    refine (path_assoc _ _ _@ _).
    do 2 refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (map_on_sem_endpoint_one_types_natural l f z).
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    exact (eqtohomot hf z).
  Qed.
  
  Definition path_alg_path_groupoid_mor
             {X Y : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             {f : X --> Y}
             {hX : sem_endpoint_one_types l X ~ sem_endpoint_one_types r X}
             {hY : sem_endpoint_one_types l Y ~ sem_endpoint_one_types r Y}
             (hf : @mor_disp _ D X Y hX hY f)
    : nat_trans_comp
        (post_whisker
           (path_alg_path_groupoid_ob hX)
           (poly_act_functor
              I
              (one_type_to_groupoid (pr1 X)) (one_type_to_groupoid (pr1 Y))
              (function_to_functor (pr1 f))))
        (pr1 (psnaturality_of
               (sem_endpoint_grpd r)
               (# (total_prealg_path_groupoid A) f)))
      =
      nat_trans_comp
        (pr1 (psnaturality_of
                (sem_endpoint_grpd l)
                (# (total_prealg_path_groupoid A) f)))
        (pre_whisker
           (poly_act_functor_data
              S
              (one_type_to_groupoid (pr1 X)) (one_type_to_groupoid (pr1 Y))
              (function_to_functor (pr1 f)))
           (path_alg_path_groupoid_ob hY)).
  Proof.
    use nat_trans_eq.
    { apply homset_property. }
    exact (path_alg_path_groupoid_mor_equation hf).
  Qed.
End LiftPathGroupoid.
