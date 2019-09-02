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
Require Export hit_path_algebra_biadj.lift_gquot.
Require Export hit_path_algebra_biadj.lift_path_groupoid.
Require Import hit_path_algebra_biadj.unit.
Require Import hit_path_algebra_biadj.counit.

Local Definition TODO {A : UU} : A.
Admitted.

Local Open Scope cat.

Section LiftAdd2CellBiadj.
  Context {A S : poly_code}
          (l r : endpoint A S I).

  Local Notation "'D1'" := (add_cell_disp_cat
                              (disp_alg_bicat (⦃ A ⦄))
                              (⦃ S ⦄)
                              (⦃ I ⦄)
                              (sem_endpoint_grpd l)
                              (sem_endpoint_grpd r)).

  Local Notation "'D2'" := (add_cell_disp_cat
                              (disp_alg_bicat (⟦ A ⟧))
                              (⟦ S ⟧)
                              (⟦ I ⟧)
                              (sem_endpoint_one_types l)
                              (sem_endpoint_one_types r)).
  
  Definition add2cell_disp_biadjunction
    : disp_left_biadj_data
        D1 D2
        (prealg_biadjunction A)
        (lift_gquot_add2cell l r).
  Proof.
    use disp_cell_unit_biadjunction.
    - exact (@path_alg_path_groupoid_ob _ _ l r).
    - exact (@path_alg_path_groupoid_mor _ _ l r).
    - exact (add2cell_lift_unit l r).
    - exact (add2cell_lift_counit l r).
  Defined.
End LiftAdd2CellBiadj.

Definition hit_path_algebra_gquot
           (Σ : hit_signature)
  : psfunctor (hit_path_algebra_grpd Σ) (hit_path_algebra_one_types Σ).
Proof.
  use total_psfunctor.
  - exact (total_psfunctor
             _ _
             gquot_psfunctor
             (prealg_gquot (point_constr Σ))).
  - use disp_depprod_psfunctor.
    + intro i.
      exact (lift_gquot_add2cell (path_left Σ i) (path_right Σ i)).
    + intro i.
      apply disp_2cells_isaprop_add_cell.
    + intro i.
      apply disp_locally_groupoid_add_cell.
Defined.

Definition hit_path_algebra_biadjunction
           (Σ : hit_signature)
  := total_left_biadj_data
       _
       _
       (disp_depprod_biadjunction
          (total_left_biadj_data _ _ (prealg_disp_biadjunction (point_constr Σ)))
          (λ (i : path_label Σ), lift_gquot_add2cell (path_left Σ i) (path_right Σ i))
          (λ i, add2cell_disp_biadjunction (path_left Σ i) (path_right Σ i))
          (λ i, disp_2cells_isaprop_add_cell _ _ _ _ _)
          (λ i, disp_locally_groupoid_add_cell _ _ _ _ _)
          (λ i, disp_2cells_isaprop_add_cell _ _ _ _ _)
          (λ i, disp_locally_groupoid_add_cell _ _ _ _ _)).
(*
Section LiftPseudofunctors.
  Context {A S : poly_code}
          (l r : endpoint A S I).

  Local Notation "'D1'" := (add_cell_disp_cat
                              (disp_alg_bicat (⦃ A ⦄))
                              (⦃ S ⦄)
                              (⦃ I ⦄)
                              (sem_endpoint_grpd l)
                              (sem_endpoint_grpd r)).

  Local Notation "'D2'" := (add_cell_disp_cat
                              (disp_alg_bicat (⟦ A ⟧))
                              (⟦ S ⟧)
                              (⟦ I ⟧)
                              (sem_endpoint_one_types l)
                              (sem_endpoint_one_types r)).

  Definition lift_gquot_add2cell_obj
             (G : total_bicat (disp_alg_bicat ⦃ A ⦄))
             (p : pr1 (sem_endpoint_grpd l G) ⟹ pr1 (sem_endpoint_grpd r G))
             (z : poly_act S (gquot (pr1 G)))
    : sem_endpoint_one_types
        l
        (total_psfunctor
           _ _ _
           (disp_alg_psfunctor gquot_psfunctor (poly_gquot A))
           G)
        z
      =
      sem_endpoint_one_types
        r
        (total_psfunctor
           _ _ _
           (disp_alg_psfunctor gquot_psfunctor (poly_gquot A))
           G)
        z.
  Admitted.

  Definition lift_gquot_add2cell_mor
             {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
             {F : G₁ --> G₂}
             {hG₁ : pr1 ((sem_endpoint_grpd l) G₁) ⟹ pr1 ((sem_endpoint_grpd r) G₁)}
             {hG₂ : pr1 ((sem_endpoint_grpd l) G₂) ⟹ pr1 ((sem_endpoint_grpd r) G₂)}
             (ff : @mor_disp _ D1 _ _ hG₁ hG₂ F)
             (z : poly_act S (gquot (pr1 G₁)))
    : UU.
  Proof.
    (*
    refine (maponpaths (gquot_functor_map (pr1 F)) (lift_gquot_add2cell_obj G₁ hG₁ z)
            @ _ 
            =
            _
            @ lift_gquot_add2cell_obj G₂ hG₂ (poly_map S (gquot_functor_map (pr1 F)) z)).
    pose (@psnaturality_of _ _ _ _ (sem_endpoint_one_types r)) as p.
    simpl in p.
    specialize (p _ _ (gquot_functor_map (pr1 F),, prealg_gquot_inv_cell A (pr2 F))).

    (psnaturality_of (sem_endpoint_one_types r)
     (gquot_functor_map (pr1 F),, prealg_gquot_inv_cell A (pr2 F))) z
     *)
  Admitted.

  Definition lift_gquot_add2cell
    : disp_psfunctor
        D1 D2
        (total_psfunctor
           _ _
           gquot_psfunctor
           (prealg_gquot A)).
  Proof.
    use disp_cell_unit_psfunctor.
    - exact lift_gquot_add2cell_obj.
    - apply TODO.
      (*abstract
        (intros G₁ G₂ F hG₁ hG₂ hF ;
         use funextsec ;
         intro z ;
      (*simpl.
      cbn.
      unfold homotcomp, homotfun, funhomotsec.
      cbn.*)
         apply TODO).*)
  Defined.


  Definition add2cell_biadjunction
    : disp_left_biadj_data
        D1 D2
        (total_left_biadj_data _ _ (algebra_disp_biadjunction A))
        lift_gquot_add2cell.
  Proof.
    use disp_cell_unit_biadjunction.
    - 
























Definition PathOver_to_square
           {X Y : UU}
           {f g : X → Y}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {q₁ : f x₁ = g x₁} {q₂ : f x₂ = g x₂}
           (s : @PathOver _ _ _ (λ z, f z = g z) q₁ q₂ p)
  : square q₂ (maponpaths f p) (maponpaths g p) q₁.
Proof.
  induction p, s.
  exact (!(pathscomp0rid _)).
Defined.

(** We need the following lemmata *)

(** For path groupoid *)
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

Definition poly_path_groupoid_is_id_is_nat
           {P : poly_code}
           {X : one_type}
           {x y : poly_act P X}
           (f : poly_act_morphism P (one_type_to_groupoid X) x y)
  : # (pr1 (pr111 (poly_path_groupoid P) X)) f @ poly_path_groupoid_is_id y
    =
    poly_path_groupoid_is_id x @ poly_act_groupoid_to_path f.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply pathscomp0rid.
  - apply pathscomp0rid.
  - induction x as [x | x], y as [y | y].
    + exact ((!(maponpathscomp0 _ _ _))
               @ (maponpaths (maponpaths inl) (IHP₁ _ _ f))
               @ maponpathscomp0 _ _ _).
    + exact (fromempty f).
    + exact (fromempty f).
    + exact ((!(maponpathscomp0 _ _ _))
               @ (maponpaths (maponpaths inr) (IHP₂ _ _ f))
               @ maponpathscomp0 _ _ _).
  - exact ((pathsdirprod_concat _ _ _ _)
             @ maponpaths (λ z, pathsdirprod z _) (IHP₁ _ _ (pr1 f))
             @ maponpaths (pathsdirprod _) (IHP₂ _ _ (pr2 f))
             @ !(pathsdirprod_concat _ _ _ _)).
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
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - (* Identity *)
    exact (pathscomp0rid _ @ !(maponpathsidfun _)).
  - (* Composition *)
    simpl ; cbn.
    apply TODO.
  - (* Left inclusion *)
    exact (pathscomp0rid _).
  - (* Right inclusion *)
    exact (pathscomp0rid _).
  - (* Left projection *)
    exact (pathscomp0rid _ @ !(maponpaths_pr1_pathsdirprod _ _)).
  - (* Right projection *)
    exact (pathscomp0rid _ @ !(maponpaths_pr2_pathsdirprod _ _)).
  - (* Pairing *)
    simpl ; cbn.
    refine ((pathsdirprod_concat _ _ _ _)
              @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_pair.
    }
    refine ((pathsdirprod_concat _ _ _ _)
              @ !_).
    refine (maponpaths (λ z, pathsdirprod z _) (IHe₁ _ _ f) @ _).
    exact (maponpaths (pathsdirprod _) (IHe₂ _ _ f)).
  - (* Constant *)
    exact (!(maponpaths_for_constant_function _ _)).
  - (* Constant map *)
    exact (pathscomp0rid _).
  - (* Constructor *)
    simpl.
    refine (!(maponpathscomp0 _ _ _) @ _ @ maponpathscomp0 _ _ _).
    apply maponpaths.
    exact (poly_path_groupoid_is_id_is_nat f).
Qed.

(** For groupoid quotient *)
Definition test
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (z : poly_act S (gquot (pr1 G)))
  : (sem_endpoint_one_types e)
      ((total_psfunctor (disp_alg_bicat ⦃ A ⦄) (disp_alg_bicat (⟦ A ⟧)) gquot_psfunctor
                        (disp_alg_psfunctor gquot_psfunctor (poly_gquot A))) G) z
    =
    gquot_poly (gquot_functor_map (sem_endpoint_grpd e G) (poly_gquot S (pr1 G) z)).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - (* Identity *)
    refine (!(gquot_poly_poly_gquot _ z) @ _).
    apply maponpaths.
    exact (gquot_functor_identity _ _).
  - (* Composition *)
    apply TODO.
  - (* Left inclusion *)
    refine (!(gquot_poly_poly_gquot (P + Q) (inl z)) @ _).
    apply maponpaths.
    apply TODO.
  - (* Right inclusion *)
    refine (!(gquot_poly_poly_gquot (P + Q) (inr z)) @ _).
    apply maponpaths.
    apply TODO.
  - (* Left projection *)
    refine (!(gquot_poly_poly_gquot P (pr1 z)) @ _).
    apply maponpaths.
    apply TODO.
  - (* Right projection *)
    refine (!(gquot_poly_poly_gquot Q (pr2 z)) @ _).
    apply maponpaths.
    apply TODO.
  - (* Pairing *)
    apply TODO.
  - (* Constant *)
    refine (!(gquot_poly_poly_gquot (C T) t) @ _).
    apply maponpaths.
    apply TODO.
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    apply TODO.
Defined.

(** Now we put it all together *)
Section LiftPseudofunctors.
  Context {A S : poly_code}
          (l r : endpoint A S I).
  
  Local Notation "'D1'" := (add_cell_disp_cat
                              (disp_alg_bicat (⦃ A ⦄))
                              (⦃ S ⦄)
                              (⦃ I ⦄)
                              (sem_endpoint_grpd l)
                              (sem_endpoint_grpd r)).

  Local Notation "'D2'" := (add_cell_disp_cat
                              (disp_alg_bicat (⟦ A ⟧))
                              (⟦ S ⟧)
                              (⟦ I ⟧)
                              (sem_endpoint_one_types l)
                              (sem_endpoint_one_types r)).

  (** Lift of `gquot` *)
  Definition lift_gquot_add2cell_obj
             (G : total_bicat (disp_alg_bicat ⦃ A ⦄))
             (p : pr1 (sem_endpoint_grpd l G) ⟹ pr1 (sem_endpoint_grpd r G))
             (z : poly_act S (gquot (pr1 G)))
    : sem_endpoint_one_types
        l
        (total_psfunctor
            _ _ _
            (disp_alg_psfunctor gquot_psfunctor (poly_gquot A))
            G)
        z
      =
      sem_endpoint_one_types
        r
        (total_psfunctor
           _ _ _
           (disp_alg_psfunctor gquot_psfunctor (poly_gquot A))
           G)
        z
    := (test l z)
         @ maponpaths gquot_poly (gquot_functor_cell p ((poly_gquot S) (pr1 G) z))
         @ !(test r z).

  Definition lift_gquot_add2cell_mor
             {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
             {F : G₁ --> G₂}
             {xx : pr1 ((sem_endpoint_grpd l) G₁) ⟹ pr1 ((sem_endpoint_grpd r) G₁)}
             {yy : pr1 ((sem_endpoint_grpd l) G₂) ⟹ pr1 ((sem_endpoint_grpd r) G₂)}
             (ff : @mor_disp _ D1 _ _ xx yy F)
             (z : poly_act S (gquot (pr1 G₁)))
    : maponpaths (gquot_functor_map (pr1 F)) (lift_gquot_add2cell_obj _ xx z)
      @ (pr1 (psnaturality_of
                (sem_endpoint_one_types r)
                (# (total_psfunctor
                      _ _ gquot_psfunctor
                      (prealg_gquot A)) F))
           z)
      =
      (pr1(psnaturality_of
         (sem_endpoint_one_types l)
         (# (total_psfunctor
               _ _ gquot_psfunctor
               (prealg_gquot A)) F)))
        z
        @ lift_gquot_add2cell_obj _ yy (poly_map S (gquot_functor_map (pr1 F)) z).
  Proof.
    apply TODO.
  Qed.

  Definition lift_gquot_add2cell
    : disp_psfunctor
        D1 D2
        (total_psfunctor
           _ _
           gquot_psfunctor
           (prealg_gquot A)).
  Proof.
    use disp_cell_unit_psfunctor.
    - exact lift_gquot_add2cell_obj.
    - intros x y f xx yy ff.
      use funextsec.
      intro z.
      simpl.
      cbn.
      unfold homotcomp, homotfun, funhomotsec.
      simpl.
      cbn.
      exact (lift_gquot_add2cell_mor ff).
  Defined.

  (** Lift of `path_groupoid` on objects *)
  Definition lift_path_groupoid_add_2cell_ob_data
             {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             (p : ∏ (x : poly_act S (pr1 X : one_type)),
                  sem_endpoint_one_types l X x
                  =
                  sem_endpoint_one_types r X x)
    : nat_trans_data
        (pr1
           ((sem_endpoint_grpd l)
              (one_type_to_groupoid
                 (pr1 X),,
                 (poly_path_groupoid A) (pr1 X) ∙ function_to_functor (pr2 X))))
        (pr1
           ((sem_endpoint_grpd r)
              (one_type_to_groupoid
                 (pr1 X),,
                 (poly_path_groupoid A) (pr1 X) ∙ function_to_functor (pr2 X))))
    := λ z, path_groupoid_endpoint l z @ p z @ !(path_groupoid_endpoint r z).

  Definition lift_path_groupoid_add_2cell_ob_is_nat_trans
             {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             (p : ∏ (x : poly_act S (pr1 X : one_type)),
                  sem_endpoint_one_types l X x
                  =
                  sem_endpoint_one_types r X x)
    : is_nat_trans _ _ (lift_path_groupoid_add_2cell_ob_data p).
  Proof.
    intros z₁ z₂ f.
    simpl in *.
    cbn.
    unfold lift_path_groupoid_add_2cell_ob_data.
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

  Definition lift_path_groupoid_add_2cell_ob
             {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             (p : ∏ (x : poly_act S (pr1 X : one_type)),
                  sem_endpoint_one_types l X x
                  =
                  sem_endpoint_one_types r X x)
    : pr1
        ((sem_endpoint_grpd l)
           (one_type_to_groupoid
              (pr1 X),,
              (poly_path_groupoid A) (pr1 X) ∙ function_to_functor (pr2 X)))
      ⟹
      pr1
        ((sem_endpoint_grpd r)
           (one_type_to_groupoid
              (pr1 X),,
              (poly_path_groupoid A) (pr1 X) ∙ function_to_functor (pr2 X))).
  Proof.
    use make_nat_trans.
    - exact (lift_path_groupoid_add_2cell_ob_data p).
    - exact (lift_path_groupoid_add_2cell_ob_is_nat_trans p).
  Defined.

  (** Lift of `path_groupoid` on morphisms *)

  
  (** For unit *)

  (** For counit *)

  (** Putting it all together *)
  Definition add2cell_biadjunction
    : disp_left_biadj_data
        D1 D2
        (total_left_biadj_data _ _ (algebra_disp_biadjunction A))
        lift_gquot_add2cell.
  Proof.
    use disp_cell_unit_biadjunction.
    - exact (λ _ p, lift_path_groupoid_add_2cell_ob p).
    - (* intros X Y f XX YY ff.
      use nat_trans_eq.
      { apply TODO. }
      intro z.
      simpl.
      cbn.
      simpl in *.
      cbn in *.
      unfold lift_path_groupoid_add_2cell_ob_data.
      unfold lift*)
      apply TODO.
    - apply TODO.
    - apply TODO.
  Defined.
End LiftPseudofunctors.
*)
