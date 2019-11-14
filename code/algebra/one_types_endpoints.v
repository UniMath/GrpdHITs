(** Interpretation of endpoints in 1-types *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
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
Require Import algebra.one_types_polynomials.

Local Open Scope cat.

Opaque comp_psfunctor.

Definition sem_endpoint_UU_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : UU}
           {cX : poly_act A X → X}
           {cY : poly_act A Y → Y}
           {f : X → Y}
           (ef : ((λ x, f (cX x)) ~ (λ x, cY (poly_map A f x))))
           (x : poly_act P X)
  : poly_map Q f (sem_endpoint_UU e cX x)
    =
    sem_endpoint_UU e cY (poly_map P f x).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ g | ].
  - (* Identity *)
    exact (idpath _).
  - (* Composition *)
    exact (IHe₂ (sem_endpoint_UU e₁ cX x)
           @ maponpaths (sem_endpoint_UU e₂ cY) (IHe₁ x)).
  - (* Left inclusion *)
    exact (idpath _).
  - (* Right inclusion *)
    exact (idpath _).
  - (* Left projection *)
    exact (idpath _).
  - (* Right projection *)
    exact (idpath _).
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  - (* Constant *)
    exact (idpath _).
  - (* Constant map *)
    exact (idpath _).
  - (* Constructor *)
    exact (ef x).
Defined.
  
Definition sem_endpoint_one_types_data
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans_data
      (comp_psfunctor (⟦ P ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))))
      (comp_psfunctor (⟦ Q ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧)))).
Proof.
  use make_pstrans_data.
  - exact (λ X, sem_endpoint_UU e (pr2 X)).
  - intros X Y f.
    use make_invertible_2cell.
    + exact (λ x, sem_endpoint_UU_natural e (pr12 f) x).
    + apply one_type_2cell_iso.
Defined.

Definition sem_endpoint_UU_natural_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : UU}
           {cX : poly_act A X → X}
           {cY : poly_act A Y → Y}
           {f g : X → Y}
           {ef : ((λ x, f (cX x)) ~ (λ x, cY (poly_map A f x)))}
           {eg : ((λ x, g (cX x)) ~ (λ x, cY (poly_map A g x)))}
           {αp : f ~ g}
           (αh : (λ x : poly_act A X, αp (cX x) @ eg x)
                 =
                 (λ x : poly_act A X, ef x @ maponpaths cY (poly_homot A αp x)))
           (x : poly_act P X)
  : poly_homot Q αp (sem_endpoint_UU e cX x)
    @ sem_endpoint_UU_natural e eg x
    =
    sem_endpoint_UU_natural e ef x
    @ maponpaths (sem_endpoint_UU e cY) (poly_homot P αp x).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    exact (pathscomp0rid _ @ !(maponpathsidfun _)).
  - (* Composition *)
    exact (path_assoc _ _ _
           @ maponpaths (λ z, z @ _) (IHe₂ (sem_endpoint_UU e₁ cX x))
           @ !(path_assoc _ _ _)
           @ maponpaths
               (λ z, _ @ z)
               (!(maponpathscomp0 _ _ _)
                @ maponpaths
                    (maponpaths (sem_endpoint_UU e₂ cY))
                    (IHe₁ x)
                @ maponpathscomp0 _ _ _
                @ maponpaths
                    (λ z, _ @ z)
                    (maponpathscomp _ _ _))
           @ path_assoc _ _ _).
  - (* Left inclusion *)
    exact (pathscomp0rid _).
  - (* Right inclusion *)
    exact (pathscomp0rid _).
  - (* Left projection *)
    exact (pathscomp0rid _ @ !(maponpaths_pr1_pathsdirprod _ _)).
  - (* Right projection *)
    exact (pathscomp0rid _ @ !(maponpaths_pr2_pathsdirprod _ _)).
  - (* Pairing *)
    exact (pathsdirprod_concat _ _ _ _
           @ paths_pathsdirprod (IHe₁ x) (IHe₂ x)
           @ !(pathsdirprod_concat _ _ _ _)
           @ maponpaths
               (λ z, _ @ z)
               (!(maponpaths_prod_path _ _ _))).
  - (* Constant *)
    exact (!(maponpaths_for_constant_function _ _)).
  - (* Constant map *)
    exact (idpath _).
  - (* Constructor *)
    exact (eqtohomot αh x).
Qed.

Definition sem_endpoint_UU_natural_id
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : one_type}
           (c : poly_act A X → X)
           (x : poly_act P X)
  : (poly_id Q X (sem_endpoint_UU e c x)
     @ poly_homot Q (λ z, idpath z) (sem_endpoint_UU e c x))
    @ sem_endpoint_UU_natural e (λ z, maponpaths c (poly_id A X z)) x
    =
    maponpaths
      (sem_endpoint_UU e c)
      (poly_id P X x @ poly_homot P (λ z, idpath z) x).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    exact (pathscomp0rid _ @ !(maponpathsidfun _)).
  - (* Composition *)
    exact (path_assoc _ _ _
           @ maponpaths (λ z, z @ _) (IHe₂ (sem_endpoint_UU e₁ c x))
           @ !(maponpathscomp0 _ _ _)
           @ maponpaths
               (maponpaths (sem_endpoint_UU e₂ c))
               (IHe₁ x)
           @ maponpathscomp _ _ _).
  - (* Left inclusion *)
    exact (pathscomp0rid _ @ !(maponpathscomp0 _ _ _)).
  - (* Right inclusion *)
    exact (pathscomp0rid _ @ !(maponpathscomp0 _ _ _)).
  - (* Left projection *)
    exact (pathscomp0rid _
           @ !(maponpaths_pr1_pathsdirprod _ _)
           @ maponpaths (maponpaths pr1) (!(pathsdirprod_concat _ _ _ _))).
  - (* Right projection *)
    exact (pathscomp0rid _
           @ !(maponpaths_pr2_pathsdirprod _ _)
           @ maponpaths (maponpaths dirprod_pr2) (!(pathsdirprod_concat _ _ _ _))).
  - (* Pairing *)
    exact (maponpaths
             (λ z, z @ _)
             (pathsdirprod_concat _ _ _ _)
           @ pathsdirprod_concat _ _ _ _
           @ paths_pathsdirprod (IHe₁ x) (IHe₂ x)
           @ !(maponpaths_prod_path _ _ _)).
  - (* Constant *)
    exact (!(maponpaths_for_constant_function _ _)).
  - (* Constant map *)
    exact (idpath _).
  - (* Constructor *)
    exact (maponpaths
             (maponpaths c)
             (!(pathscomp0rid _)
              @ maponpaths
                  (λ z, _ @ z)
                  (!(eqtohomot
                       (psfunctor_id2 (sem_poly_one_types A) (λ (x : X), x))
                       x)))).
Qed.

Definition sem_endpoint_UU_natural_comp
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y Z : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (f : X --> Y)
           (g : Y --> Z)
           (x : poly_act P (pr1 X : one_type))
  : (poly_comp Q (pr1 f) (pr1 g) (sem_endpoint_UU e (pr2 X) x)
    @ poly_homot Q (λ x0, idpath (pr1 g (pr1 f x0))) (sem_endpoint_UU e (pr2 X) x))
    @ sem_endpoint_UU_natural
        e
        (λ x0,
         (((maponpaths (pr1 g) (pr12 f x0)
            @ idpath (pr1 g (pr2 Y (poly_map A (pr1 f) x0))))
            @ (pr12 g) (poly_map A (pr1 f) x0))
            @ idpath (pr2 Z (poly_map A (pr1 g) (poly_map A (pr1 f) x0))))
            @ maponpaths (pr2 Z) (poly_comp A (pr1 f) (pr1 g) x0))
        x
    =
    (((maponpaths
         (poly_map Q (pr1 g))
         (sem_endpoint_UU_natural e (pr12 f) x)
    @ idpath (poly_map Q (pr1 g) (sem_endpoint_UU e (pr2 Y) (poly_map P (pr1 f) x))))
    @ sem_endpoint_UU_natural e (pr12 g) (poly_map P (pr1 f) x))
    @ idpath (sem_endpoint_UU e (pr2 Z) (poly_map P (pr1 g) (poly_map P (pr1 f) x))))
    @ maponpaths
        (sem_endpoint_UU e (pr2 Z))
        (poly_comp P (pr1 f) (pr1 g) x
         @ poly_homot P (λ x0, idpath (pr1 g (pr1 f x0))) x).
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpaths_2.
    apply pathscomp0rid.
  }
  etrans.
  {
    do 2 apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply (eqtohomot (psfunctor_id2 (⟦ P ⟧) (λ z, pr1 g (pr1 f z)))).
    }
    apply pathscomp0rid.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply (eqtohomot (psfunctor_id2 (⟦ Q ⟧) (λ z, pr1 g (pr1 f z)))).
    }
    apply pathscomp0rid.
  }
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    exact (pathscomp0rid _ @ !(maponpathsidfun _)).
  - (* Composition *)
    assert (poly_comp
              R (pr1 f) (pr1 g)
              (sem_endpoint_UU e₂ (pr2 X) (sem_endpoint_UU e₁ (pr2 X) x))
            @ sem_endpoint_UU_natural e₂
                (λ x0,
                 (((maponpaths (pr1 g) ((pr12 f) x0)
                    @ idpath (pr1 g (pr2 Y (poly_map A (pr1 f) x0))))
                    @ (pr12 g) (poly_map A (pr1 f) x0))
                    @ idpath (pr2 Z (poly_map A (pr1 g) (poly_map A (pr1 f) x0))))
            @ maponpaths
                (pr2 Z)
                (poly_comp A (pr1 f) (pr1 g) x0)) (sem_endpoint_UU e₁ (pr2 X) x)
            @ maponpaths
                (sem_endpoint_UU e₂ (pr2 Z))
                (sem_endpoint_UU_natural
                   e₁
                   (λ x0,
                    (((maponpaths (pr1 g) ((pr12 f) x0)
                       @ idpath (pr1 g (pr2 Y (poly_map A (pr1 f) x0))))
                       @ (pr12 g) (poly_map A (pr1 f) x0))
                       @ idpath _)
                      @ maponpaths (pr2 Z) (poly_comp A (pr1 f) (pr1 g) x0))
                   x)
            =
            (maponpaths
               (poly_map R (pr1 g))
               (sem_endpoint_UU_natural
                  e₂ (pr12 f)
                  (sem_endpoint_UU e₁ (pr2 X) x)
            @ maponpaths
                (sem_endpoint_UU e₂ (pr2 Y))
                (sem_endpoint_UU_natural e₁ (pr12 f) x))
            @ sem_endpoint_UU_natural
                e₂ (pr12 g)
                (sem_endpoint_UU e₁ (pr2 Y) (poly_map P (pr1 f) x))
            @ maponpaths
                (sem_endpoint_UU e₂ (pr2 Z))
                (sem_endpoint_UU_natural e₁ (pr12 g) (poly_map P (pr1 f) x)))
            @ maponpaths
                (λ x0, sem_endpoint_UU e₂ (pr2 Z) (sem_endpoint_UU e₁ (pr2 Z) x0))
                (poly_comp P (pr1 f) (pr1 g) x))
      as goal.
    {
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply IHe₂.
      }
      clear IHe₂.
      refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
      refine (!(path_assoc _ _ _) @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp0 (poly_map R (pr1 g)) _ _).
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          exact (!(maponpathscomp0 (sem_endpoint_UU e₂ (pr2 Z)) _ _)).
        }
        apply maponpaths.
        apply IHe₁.
      }
      clear IHe₁.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathscomp _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (!(path_assoc _ _ _)).
        }
        exact (maponpathscomp0 _ _ _).
      }
      refine (path_assoc _ _ _ @ _).
      refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply maponpathscomp.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp.
      }
      exact (homotsec_natural'
               (sem_endpoint_UU_natural e₂ (pr12 g))
               (sem_endpoint_UU_natural e₁ (pr12 f) x)).
    }
    exact goal.
  - (* Left inclusion *)
    exact (pathscomp0rid _).
  - (* Right inclusion *)
    exact (pathscomp0rid _).
  - (* Left projection *)
    refine (pathscomp0rid _ @ _).
    refine (!_).
    exact (maponpaths_pr1_pathsdirprod _ _).
  - (* Right projection *)
    refine (pathscomp0rid _ @ _).
    refine (!_).
    exact (maponpaths_pr2_pathsdirprod _ _).
  - (* Pairing *)
    refine (!_).
    etrans.
    {
      refine (maponpaths (λ z, _ @ z) _).
      apply maponpaths_prod_path.
    }
    etrans.
    {
      refine (maponpaths (λ z, z @ _) _).
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        refine (!_).
        apply maponpaths_pathsdirprod.
      }
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply pathsdirprod_concat.
    }
    refine (!_).
    etrans.
    {
      apply pathsdirprod_concat.
    }
    exact (paths_pathsdirprod (IHe₁ x) (IHe₂ x)).
  - (* Constant *)
    exact (!(maponpaths_for_constant_function _ _)).
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    etrans.
    {
      refine (maponpaths (λ z, z @ maponpaths _ _) _).
      etrans.
      {
        apply pathscomp0rid.
      }
      apply maponpaths_2.
      apply pathscomp0rid.
    }
    apply idpath.
Qed.
  
Definition sem_endpoint_one_types_is_pstrans
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : is_pstrans (sem_endpoint_one_types_data e).
Proof.
  repeat split.
  - intros X Y f g α.
    use funextsec.
    exact (sem_endpoint_UU_natural_natural e (pr2 α)).
  - intros X.
    use funextsec.
    exact (sem_endpoint_UU_natural_id e (pr2 X)).
  - intros X Y Z f g.
    use funextsec.
    exact (sem_endpoint_UU_natural_comp e f g).
Qed.

Definition sem_endpoint_one_types
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans
      (comp_psfunctor (⟦ P ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧))))
      (comp_psfunctor (⟦ Q ⟧) (pr1_psfunctor (disp_alg_bicat (⟦ A ⟧)))).
Proof.
  use make_pstrans.
  - exact (sem_endpoint_one_types_data e).
  - exact (sem_endpoint_one_types_is_pstrans e).
Defined.
