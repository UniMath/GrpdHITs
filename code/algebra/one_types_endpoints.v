(** Interpretation of endpoints in 1-types *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Constant.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.

Local Open Scope cat.

(** Endpoints related to the sum *)
Section Sum.
  Variable (P Q : poly_code).

  Definition inl_transformation_data
    : pstrans_data (⟦ P ⟧) (⟦ P + Q ⟧).
  Proof.
    use make_pstrans_data.
    - exact (λ X x, inl x).
    - intros X Y f.
      use make_invertible_2cell.
      + exact (λ _, idpath _).
      + apply one_type_2cell_iso.
  Defined.

  Definition inl_transformation_is_pstrans
    : is_pstrans inl_transformation_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      intro x.
      apply pathscomp0rid.
    - intros X.
      use funextsec.
      intro x.
      apply pathscomp0rid.
    - intros X Y Z f g.
      use funextsec.
      intro x.
      apply pathscomp0rid.
  Qed.

  Definition inl_transformation
    : pstrans (⟦ P ⟧) (⟦ P + Q ⟧).
  Proof.
    use make_pstrans.
    - exact inl_transformation_data.
    - exact inl_transformation_is_pstrans.
  Defined.

  Definition inr_transformation_data
    : pstrans_data (⟦ Q ⟧) (⟦ P + Q ⟧).
  Proof.
    use make_pstrans_data.
    - exact (λ X x, inr x).
    - intros X Y f.
      use make_invertible_2cell.
      + exact (λ _, idpath _).
      + apply one_type_2cell_iso.
  Defined.

  Definition inr_transformation_is_pstrans
    : is_pstrans inr_transformation_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      intro x.
      apply pathscomp0rid.
    - intros X.
      use funextsec.
      intro x.
      apply pathscomp0rid.
    - intros X Y Z f g.
      use funextsec.
      intro x.
      apply pathscomp0rid.
  Qed.

  Definition inr_transformation
    : pstrans (⟦ Q ⟧) (⟦ P + Q ⟧).
  Proof.
    use make_pstrans.
    - exact inr_transformation_data.
    - exact inr_transformation_is_pstrans.
  Defined.
End Sum.

(** Lemmas for product endpoints *)
Definition maponpaths_pr1_pathsdirprod
           {X Y : UU}
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ y₂ : Y}
           (q : y₁ = y₂)
  : maponpaths pr1 (pathsdirprod p q) = p.
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.

Definition maponpaths_pr2_pathsdirprod
           {X Y : UU}
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ y₂ : Y}
           (q : y₁ = y₂)
  : maponpaths (λ (z : X × Y), pr2 z) (pathsdirprod p q) = q.
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.

Definition maponpaths_pr1_dirprodf_path
           {X₁ X₂ Y₁ Y₂ : UU}
           {f₁ g₁ : X₁ → Y₁}
           {f₂ g₂ : X₂ → Y₂}
           (p₁ : f₁ ~ g₁)
           (p₂ : f₂ ~ g₂)
           (x : X₁ × X₂)
  : maponpaths pr1 (dirprodf_path p₁ p₂ x) = p₁ (pr1 x).
Proof.
  apply maponpaths_pr1_pathsdirprod.
Defined.

Definition maponpaths_pr2_dirprodf_path
           {X₁ X₂ Y₁ Y₂ : UU}
           {f₁ g₁ : X₁ → Y₁}
           {f₂ g₂ : X₂ → Y₂}
           (p₁ : f₁ ~ g₁)
           (p₂ : f₂ ~ g₂)
           (x : X₁ × X₂)
  : maponpaths (λ (z : _ × _), pr2 z) (dirprodf_path p₁ p₂ x) = p₂ (pr2 x).
Proof.
  apply maponpaths_pr2_pathsdirprod.
Defined.

(** Projections of endpoints *)
Section Prod.
  Variable (P Q : poly_code).

  Definition pr1_transformation_data
    : pstrans_data (⟦ P * Q ⟧) (⟦ P ⟧).
  Proof.
    use make_pstrans_data.
    - exact (λ X x, pr1 x).
    - intros X Y f.
      use make_invertible_2cell.
      + intro x.
        apply idpath.
      + apply one_type_2cell_iso.
  Defined.

  Definition pr1_transformation_is_pstrans
    : is_pstrans pr1_transformation_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      intro x.
      refine (pathscomp0rid _ @ !_).
      apply maponpaths_pr1_dirprodf_path.
    - intro X.
      use funextsec.
      intro x.
      refine (pathscomp0rid _ @ !_).
      exact (maponpaths_pr1_dirprodf_path _ _ x).
    - intros X Y Z f g.
      use funextsec.
      intro x.
      refine (pathscomp0rid _ @ !_).
      exact (maponpaths_pr1_dirprodf_path _ _ x).
  Qed.

  Definition pr1_transformation
    : pstrans (⟦ P * Q ⟧) (⟦ P ⟧).
  Proof.
    use make_pstrans.
    - exact pr1_transformation_data.
    - exact pr1_transformation_is_pstrans.
  Defined.

  Definition pr2_transformation_data
    : pstrans_data (⟦ P * Q ⟧) (⟦ Q ⟧).
  Proof.
    use make_pstrans_data.
    - exact (λ X x, pr2 x).
    - intros X Y f.
      use make_invertible_2cell.
      + intro x.
        apply idpath.
      + apply one_type_2cell_iso.
  Defined.

  Definition pr2_transformation_is_pstrans
    : is_pstrans pr2_transformation_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      intro x.
      refine (pathscomp0rid _ @ !_).
      apply maponpaths_pr2_dirprodf_path.
    - intro X.
      use funextsec.
      intro x.
      refine (pathscomp0rid _ @ !_).
      exact (maponpaths_pr2_dirprodf_path _ _ x).
    - intros X Y Z f g.
      use funextsec.
      intro x.
      refine (pathscomp0rid _ @ !_).
      exact (maponpaths_pr2_dirprodf_path _ _ x).
  Qed.

  Definition pr2_transformation
    : pstrans (⟦ P * Q ⟧) (⟦ Q ⟧).
  Proof.
    use make_pstrans.
    - exact pr2_transformation_data.
    - exact pr2_transformation_is_pstrans.
  Defined.
End Prod.

(** Needed for pairing *)
Definition path_pathsdirprod
           {X Y : UU}
           {x₁ x₂ : X}
           {p₁ p₂ : x₁ = x₂}
           (s₁ : p₁ = p₂)
           {y₁ y₂ : Y}
           {q₁ q₂ : y₁ = y₂}
           (s₂ : q₁ = q₂)
  : pathsdirprod p₁ q₁
    =
    pathsdirprod p₂ q₂
  := maponpaths (λ z, pathsdirprod z _) s₁ @ maponpaths (pathsdirprod _) s₂.

Definition maponpaths_pair
           {X Y₁ Y₂ : UU}
           (f₁ : X → Y₁)
           (f₂ : X → Y₂)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
  : maponpaths (λ x, f₁ x ,, f₂ x) p
    =
    pathsdirprod
      (maponpaths f₁ p)
      (maponpaths f₂ p).
Proof.
  induction p.
  apply idpath.
Defined.

(** Pairing of endpoints *)
Section Pair.
  Context {B : bicat}
          {F : psfunctor B one_types}
          (P Q R : poly_code).
  Variable (α : pstrans
                  (ps_comp (⟦ P ⟧) F)
                  (ps_comp (⟦ Q ⟧) F))
           (β : pstrans
                  (ps_comp (⟦ P ⟧) F)
                  (ps_comp (⟦ R ⟧) F)).

  Definition pair_transformation_data
    : pstrans_data
        (ps_comp (⟦ P ⟧) F)
        (ps_comp (⟦ Q * R ⟧) F).
  Proof.
    use make_pstrans_data.
    - exact (λ X x, α X x ,, β X x).
    - intros X Y f.
      use make_invertible_2cell.
      + intros x.
        use pathsdirprod.
        * exact (pr1 (psnaturality_of α f) x).
        * exact (pr1 (psnaturality_of β f) x).
      + apply one_type_2cell_iso.
  Defined.

  Definition pair_transformation_is_pstrans
    : is_pstrans pair_transformation_data.
  Proof.
    repeat split.
    - intros X Y f g p.
      use funextsec.
      intro x.
      refine (pathsdirprod_concat _ _ _ _ @ _).
      refine (_ @ maponpaths (λ p, _ @ p) (!(maponpaths_pair _ _ _))).
      refine (_ @ !(pathsdirprod_concat _ _ _ _)).
      apply path_pathsdirprod.
      + exact (eqtohomot (psnaturality_natural α X Y f g p) x).
      + exact (eqtohomot (psnaturality_natural β X Y f g p) x).
    - intros X.
      use funextsec.
      intro x.
      refine (maponpaths (λ z, z @ _) (pathsdirprod_concat _ _ _ _) @ _).
      refine (pathsdirprod_concat _ _ _ _ @ _).
      refine (_ @ maponpaths (λ p, _ @ p) (!(maponpaths_pair _ _ _))).
      apply path_pathsdirprod.
      + exact (eqtohomot (pstrans_id α X) x).
      + exact (eqtohomot (pstrans_id β X) x).
    - intros X Y Z f g.
      use funextsec.
      intro x.
      refine (maponpaths (λ z, z @ _) (pathsdirprod_concat _ _ _ _) @ _).
      refine (pathsdirprod_concat _ _ _ _ @ _).
      refine (_ @ maponpaths (λ p, _ @ p) (!(maponpaths_pair _ _ _))).
      refine (path_pathsdirprod
                (eqtohomot (pstrans_comp α f g) x)
                (eqtohomot (pstrans_comp β f g) x)
              @ _).
      refine (!(pathsdirprod_concat _ _ _ _) @ _).
      apply (maponpaths (λ p, p @ _)).
      refine (!(pathsdirprod_concat _ _ _ _) @ _).
      apply (maponpaths (λ p, p @ _)).
      refine (!(pathsdirprod_concat _ _ _ _) @ _).
      apply (maponpaths (λ p, p @ _)).
      refine (!(pathsdirprod_concat _ _ _ _) @ _).
      apply (maponpaths (λ p, p @ _)).
      refine (!(pathsdirprod_concat _ _ _ _) @ _).
      exact (maponpaths_pathsdirprod
               _ _
               (pr1 (psnaturality_of α f) x)
               (pr1 (psnaturality_of β f) x)).
  Qed.

  Definition pair_transformation
    : pstrans
        (ps_comp (⟦ P ⟧) F)
        (ps_comp (⟦ Q * R ⟧) F).
  Proof.
    use make_pstrans.
    - exact pair_transformation_data.
    - exact pair_transformation_is_pstrans.
  Defined.
End Pair.

(** Constant endpoint *)
Section ConstantElement.
  Variable (F : psfunctor one_types one_types)
           (Y : one_type)
           (y : Y).

  Definition constant_el_data
    : pstrans_data F (constant one_types (Y : one_types)).
  Proof.
    use make_pstrans_data.
    - exact (λ _ _, y).
    - intros X₁ X₂ f.
      use make_invertible_2cell.
      + exact (λ _, idpath _).
      + apply one_type_2cell_iso.
  Defined.

  Definition constant_el_laws
    : is_pstrans constant_el_data.
  Proof.
    repeat split.
    - intros X₁ X₂ f g p.
      use funextsec.
      intro z.
      refine (!_).
      apply maponpaths_for_constant_function.
    - intros X.
      use funextsec.
      intro z.
      refine (!_).
      apply maponpaths_for_constant_function.
    - intros X₁ X₂ X₃ f g.
      use funextsec.
      intro z.
      refine (!_).
      apply maponpaths_for_constant_function.
  Qed.      
  
  Definition constant_el
    : pstrans F (constant one_types (Y : one_types)).
  Proof.
    use make_pstrans.
    - exact constant_el_data.
    - exact constant_el_laws.
  Defined.
End ConstantElement.

(** Function endpoint *)
Section ConstantFunction.
  Context {A B : one_types}
          (ψ : A --> B).

  Definition constant_fun_data
    : pstrans_data (constant one_types A) (constant one_types B).
  Proof.
    use make_pstrans_data.
    - exact (λ _, ψ).
    - intros X Y f.
      use make_invertible_2cell.
      + exact (λ _, idpath _).
      + apply one_type_2cell_iso.
  Defined.

  Definition constant_fun_is_pstrans
    : is_pstrans constant_fun_data.
  Proof.
    repeat use tpair
    ; intro ; intros ; apply idpath.
  Qed.    

  Definition constant_fun
    : pstrans (constant one_types A) (constant one_types B).
  Proof.
    use make_pstrans.
    - exact constant_fun_data.
    - exact constant_fun_is_pstrans.
  Defined.
End ConstantFunction.

Opaque ps_comp.

Definition alg_map_data
           (A : poly_code)
  : pstrans_data
      (ps_comp (⟦ A ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))))
      (ps_comp (⟦ I ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧)))).
Proof.
  use make_pstrans_data.
  - exact (λ X, pr2 X).
  - exact (λ _ _ f, pr2 f).
Defined.

Definition alg_map_data_is_pstrans
           (A : poly_code)
  : is_pstrans (alg_map_data A).
Proof.
  repeat split.
  - intros X Y f g α.
    apply α.
  - intro X.
    use funextsec ; intro z.
    apply (maponpaths (maponpaths (pr2 X))).
    refine (!(pathscomp0rid _) @ _).
    exact (maponpaths
             (λ z, _ @ z)
             (!(eqtohomot (psfunctor_id2 (⟦ A ⟧) (λ (x : pr1 X : one_type), x)) z))).
  - intros X Y Z f g.
    use funextsec ; intro z.
    refine (maponpaths (λ z, _ @ (z @ _)) (_ @ _) @ _).
    { apply pathscomp0rid. }
    { exact (maponpaths (λ z, z @ _) (pathscomp0rid _)). }
    refine (!_).
    refine (maponpaths (λ z, z @ _) (_ @ _) @ _).
    { apply pathscomp0rid. }
    { exact (maponpaths (λ z, z @ _) (pathscomp0rid _)). }
    apply (maponpaths
             (pathscomp0 (maponpaths (pr1 g)
                                     ((pr12 f) z) @ (pr12 g) (poly_map A (pr1 f) z)))).
    refine (maponpaths (maponpaths (pr2 Z)) _).
    refine (!_).
    refine (!(pathscomp0rid _) @ _).
    refine (maponpaths (λ q, poly_comp A (pr1 f) (pr1 g) z @ q) _).
    exact (!(eqtohomot
               (psfunctor_id2
                  (⟦ A ⟧) (λ (x : pr1 X : one_type), pr1 g (pr1 f x)))
               z)).
Qed.

Definition alg_map
           (A : poly_code)
  : pstrans
      (ps_comp (⟦ A ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))))
      (ps_comp (⟦ I ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧)))).
Proof.
  use make_pstrans.
  - exact (alg_map_data A).
  - exact (alg_map_data_is_pstrans A).
Defined.

Definition sem_endpoint_one_types
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans
      (ps_comp (⟦ P ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))))
      (ps_comp (⟦ Q ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧)))).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T x | X Y f | ].
  - (* Identity *)
    exact (id_trans (ps_comp (⟦ P ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))))).
  - (* Composition *)
    exact (comp_trans IHe₁ IHe₂).
  - (* Left inclusion *)
    exact (inl_transformation P Q ▻ pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))).
  - (* Right inclusion *)
    exact (inr_transformation P Q ▻ pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))).
  - (* Left projection *)
    exact (pr1_transformation P Q ▻ pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))).
  - (* Right projection *)
    exact (pr2_transformation P Q ▻ pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))).
  - (* Pairing *)
    exact (pair_transformation _ _ _ IHe₁ IHe₂).
  - (* Constant *)
    exact (constant_el _ _ x ▻ pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))).
  - (* Constant map *)
    exact (constant_fun f ▻ pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))).
  - (* Constructor *)
    exact (alg_map A).
Defined.
