Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.
Require Import examples.free_algebra.

Local Open Scope cat.

Opaque hit_existence.
Opaque make_free_alg_algebra.
Opaque free_ump_1.
Opaque free_alg_ump_2.
Opaque free_alg_ump_eq.

Section FreeAlgebraFunctor.
  Variable (Σ : hit_signature).
  
  Local Definition free_alg
        (X : one_type)
    : hit_algebra_one_types (free_alg_signature Σ X)
    := pr1 (hit_existence (free_alg_signature Σ X)).

  Local Definition free_alg_is_initial
        (X : one_type)
    : is_initial _ (free_alg X).
  Proof.
    apply initial_algebra.HIT_is_initial.
    exact (pr2 (hit_existence (free_alg_signature Σ X))).
  Qed.

  Definition free_alg_psfunctor_obj
    : one_types → hit_algebra_one_types Σ
    := λ X, free_alg_is_alg (free_alg X).

  Definition free_alg_psfunctor_mor
             {X Y : one_type}
             (f : X → Y)
    : free_alg_psfunctor_obj X --> free_alg_psfunctor_obj Y.
  Proof.
    use free_ump_1.
    - apply free_alg_is_initial.
    - exact (λ x, free_alg_inc _ (f x)).
  Defined.

  Definition free_alg_psfunctor_cell
             {X Y : one_type}
             {f g : X → Y}
             (p : f ~ g)
    : free_alg_psfunctor_mor f ==> free_alg_psfunctor_mor g.
  Proof.
    use free_alg_ump_2.
    - apply free_alg_is_initial.
    - exact (λ x, free_alg_inc _ (g x)).
    - intro x.
      exact (free_alg_one_cell_on_A
               (free_alg_is_initial X)
               (free_alg_psfunctor_obj Y)
               (λ z, free_alg_inc _ (f z))
               x
             @ maponpaths (free_alg_inc (free_alg Y)) (p x)).
    - exact (free_alg_one_cell_on_A
               (free_alg_is_initial X)
               (free_alg_psfunctor_obj Y)
               (λ x, free_alg_inc _ (g x))).
  Defined.

  Definition free_alg_psfunctor_id
             (X : one_types)
    : id₁ (free_alg_psfunctor_obj X) ==> free_alg_psfunctor_mor (id₁ X).
  Proof.
    use free_alg_ump_2.
    - apply free_alg_is_initial.
    - exact (free_alg_inc _).
    - exact (λ x, idpath _).
    - exact (free_alg_one_cell_on_A
               (free_alg_is_initial X)
               (free_alg_psfunctor_obj X)
               (free_alg_inc _)).
  Defined.

  Definition free_alg_psfunctor_comp
             {X Y Z : one_type}
             (f : X → Y)
             (g : Y → Z)
    : free_alg_psfunctor_mor f · free_alg_psfunctor_mor g
      ==>
      free_alg_psfunctor_mor (λ z, g(f z)).
  Proof.
    use free_alg_ump_2.
    - apply free_alg_is_initial.
    - exact (λ x, free_alg_inc _ (g(f x))).
    - intro x.
      refine (_ @ _).
      + refine (maponpaths (alg_map_carrier (free_alg_psfunctor_mor g)) _).
        exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc _ (f z))
                 x).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial Y)
                 (free_alg_psfunctor_obj Z)
                 (λ z, free_alg_inc _ (g z))
                 _).
    - exact (free_alg_one_cell_on_A
               (free_alg_is_initial X)
               (free_alg_psfunctor_obj Z)
               (λ z, free_alg_inc _ (g(f z)))).
  Defined.

  Definition free_alg_psfunctor_data
    : psfunctor_data one_types (hit_algebra_one_types Σ).
  Proof.
    use make_psfunctor_data.
    - exact free_alg_psfunctor_obj.
    - exact @free_alg_psfunctor_mor.
    - exact @free_alg_psfunctor_cell.
    - exact @free_alg_psfunctor_id.
    - exact @free_alg_psfunctor_comp.
  Defined.

  (** Lemmata needed for the laws *)
  Local Lemma free_alg_psfunctor_cell_on_A
        {X Y : one_type}
        {f g : X → Y}
        (p : f ~ g)
        (x : X)
    : alg_2cell_carrier (free_alg_psfunctor_cell p) (alg_constr (free_alg X) (inr x))
      @ free_alg_one_cell_on_A
          (free_alg_is_initial X)
          (free_alg_psfunctor_obj Y)
          (λ z, free_alg_inc (free_alg Y) (g z))
          x
      =
      free_alg_one_cell_on_A
        (free_alg_is_initial X)
        (free_alg_psfunctor_obj Y)
        (λ z, free_alg_inc (free_alg Y) (f z))
        x
      @ maponpaths (free_alg_inc (free_alg Y)) (p x).
  Proof.
    exact (free_alg_ump_2_on_A
             (free_alg_is_initial X)
             (free_alg_psfunctor_obj Y)
             (λ z, free_alg_inc (free_alg Y) (g z))
             _
             _
             x).
  Qed.

  Local Lemma free_alg_psfunctor_id_on_A
        (X : one_type)
        (x : X)
    : alg_2cell_carrier
        (free_alg_psfunctor_id X)
        (alg_constr (free_alg X) (inr x))
      =
      !(free_alg_one_cell_on_A
          (free_alg_is_initial X)
          (free_alg_psfunctor_obj X)
          (free_alg_inc _)
          x).
  Proof.
    refine (_ @ pathscomp0lid _).
    use path_inv_rotate_rr.
    exact (free_alg_ump_2_on_A
             (free_alg_is_initial X)
             (free_alg_psfunctor_obj X)
             (free_alg_inc (free_alg X))
             _ _
             x).
  Qed.

  Local Lemma free_alg_psfunctor_comp_on_A
             {X Y Z : one_type}
             (f : X → Y) (g : Y → Z)
             (x : X)
    : alg_2cell_carrier
        (free_alg_psfunctor_comp f g)
        (alg_constr (free_alg X) (inr x))
      =
      maponpaths
        (alg_map_carrier (free_alg_psfunctor_mor g))
        (free_alg_one_cell_on_A
           (free_alg_is_initial X)
           (free_alg_psfunctor_obj Y)
           (λ z, free_alg_inc _ (f z))
           x)
      @ free_alg_one_cell_on_A
          (free_alg_is_initial Y)
          (free_alg_psfunctor_obj Z)
          (λ z, free_alg_inc _ (g z))
          (f x)
      @ !(free_alg_one_cell_on_A
            (free_alg_is_initial X)
            (free_alg_psfunctor_obj Z)
            (λ z, free_alg_inc _ (g(f z))) x).
  Proof.
    refine (_ @ !(path_assoc _ _ _)).
    use path_inv_rotate_rr.
    exact (free_alg_ump_2_on_A
             (free_alg_is_initial X)
             _ _
             _ _
             x).
  Qed.  

  Definition free_alg_psfunctor_laws
    : psfunctor_laws free_alg_psfunctor_data.
  Proof.
    refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - intros X Y f.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (f x)).
      + exact (λ x,
               free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc _ (f z))
                 x
               @ maponpaths (free_alg_inc (free_alg Y)) (idpath _)).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc _ (f z))).
      + exact (free_alg_psfunctor_cell_on_A (homotrefl f)).
      + intro x ; cbn.
        exact (!(pathscomp0rid _)).
    - intros X Y f g h τ θ.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (h x)).
      + intro x.
        exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X) (free_alg_psfunctor_obj Y)
                 (λ z, free_alg_inc (free_alg Y) (f z)) x @
                 maponpaths (free_alg_inc (free_alg Y)) (homotcomp τ θ x)).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ x, free_alg_inc (free_alg Y) (h x))).
      + exact (free_alg_psfunctor_cell_on_A (homotcomp τ θ)).
      + intro x ; cbn.
        unfold homotcomp ; simpl.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (free_alg_psfunctor_cell_on_A θ x).
        }
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          exact (free_alg_psfunctor_cell_on_A τ x).
        }
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        exact (!(maponpathscomp0 _ _ _)).
    - intros X Y f.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (f x)).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ x, free_alg_inc (free_alg Y) (f x))).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ x, free_alg_inc (free_alg Y) (f x))).
      + intro x.
        simpl ; cbn.
        apply idpath.
      + intro x.
        cbn ; unfold homotcomp, homotfun ; cbn.
        do 2 refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          do 2 apply maponpaths.
          exact (free_alg_psfunctor_cell_on_A _ x).
        }
        cbn.
        etrans.
        {
          do 2 apply maponpaths.
          apply pathscomp0rid.
        }
        refine (_ @ (pathscomp0lid _)).
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          exact (free_alg_psfunctor_comp_on_A _ _ _).
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply pathsinv0r.
          }
          apply pathscomp0rid.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (free_alg_psfunctor_id_on_A X x).
          }
          apply maponpathsinv0.
        }
        apply pathsinv0l.
    - intros X Y f.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (f x)).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ x, free_alg_inc (free_alg Y) (f x))).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Y)
                 (λ x, free_alg_inc (free_alg Y) (f x))).
      + intro x.
        simpl ; cbn.
        apply idpath.
      + intro x.
        cbn ; unfold homotcomp, funhomotsec ; cbn.
        do 2 refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          do 2 apply maponpaths.
          exact (free_alg_psfunctor_cell_on_A _ x).
        }
        etrans.
        {
          do 2 apply maponpaths.
          apply pathscomp0rid.
        }
        refine (_ @ (pathscomp0lid _)).
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          exact (free_alg_psfunctor_comp_on_A _ _ _).
        }
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (homotsec_natural'
                   (alg_2cell_carrier (free_alg_psfunctor_id Y))).
        }
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply free_alg_psfunctor_id_on_A.
          }
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          apply pathsinv0l.
        }
        simpl.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathsidfun.
        }
        apply pathsinv0r.
    - intros W X Y Z f g h.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc _ (h(g(f x)))).
      + intro x ; cbn.
        exact (maponpaths
                 (alg_map_carrier
                    (free_alg_psfunctor_mor g
                     · free_alg_psfunctor_mor h))
                 (free_alg_one_cell_on_A
                    (free_alg_is_initial W)
                    (free_alg_psfunctor_obj X)
                    (λ z, free_alg_inc (free_alg X) (f z)) x)
               @ maponpaths
                   (alg_map_carrier (free_alg_psfunctor_mor h))
                   (free_alg_one_cell_on_A
                      (free_alg_is_initial X)
                      (free_alg_psfunctor_obj Y)
                      (λ z, free_alg_inc (free_alg Y) (g z)) (f x))
               @ free_alg_one_cell_on_A
                   (free_alg_is_initial Y)
                   (free_alg_psfunctor_obj Z)
                   (λ z, free_alg_inc (free_alg Z) (h z)) (g (f x))).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial W)
                 (free_alg_psfunctor_obj Z)
                 (λ z, free_alg_inc
                         (free_alg Z)
                         (h(g(f z))))).
      + intro x ; cbn ; unfold homotcomp, funhomotsec.
        do 2 refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          do 2 apply maponpaths.
          etrans.
          {
            exact (free_alg_psfunctor_cell_on_A
                     (homotrefl (λ z, h(g(f z))))
                     x).
          }
          apply pathscomp0rid.
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (free_alg_psfunctor_comp_on_A _ _ x).
        }
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
          apply pathscomp0rid.
        }
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          exact (homotsec_natural'
                   (alg_2cell_carrier (free_alg_psfunctor_comp g h))
                   _).
        }
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (free_alg_psfunctor_comp_on_A _ _ (f x)).
        }
        etrans.
        {
          do 2 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0l.
          }
          apply pathscomp0rid.
        }
        apply idpath.
      + intro x ; cbn ; unfold homotcomp, homotfun, funhomotsec ; cbn.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (free_alg_psfunctor_comp_on_A _ _ x).
        }
        etrans.
        {
          do 2 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0l.
          }
          apply pathscomp0rid.
        }
        refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        refine (!(maponpathscomp0 _ _ _) @ _).
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply maponpathscomp.
        }
        refine (!(maponpathscomp0 _ _ _) @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (free_alg_psfunctor_comp_on_A _ _ x).
        }
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          apply pathsinv0l.
        }
        apply pathscomp0rid.
    - intros X Y Z f g₁ g₂ τ.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ x, free_alg_inc (free_alg Z) (g₂ (f x))).
      + intro x.
        exact (maponpaths
                 (alg_map_carrier (free_alg_psfunctor_mor g₁))
                 (free_alg_one_cell_on_A
                    (free_alg_is_initial X)
                    (free_alg_psfunctor_obj Y)
                    (λ z, free_alg_inc (free_alg Y) (f z)) x)
               @ free_alg_one_cell_on_A
                   (free_alg_is_initial Y)
                   (free_alg_psfunctor_obj Z)
                   (λ z, free_alg_inc (free_alg Z) (g₁ z)) (f x)
               @ maponpaths (free_alg_inc (free_alg Z)) (τ (f x))).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Z)
                 (λ z, free_alg_inc (free_alg Z) ((λ z0, g₂ (f z0)) z))).
      + intro x ; cbn.
        unfold homotcomp, funhomotsec.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (free_alg_psfunctor_cell_on_A (λ z, τ(f z)) x).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (free_alg_psfunctor_comp_on_A f g₁ x).
        }
        etrans.
        {
          do 2 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          apply pathsinv0l.
        }
        apply idpath.
      + intro x ; cbn.
        unfold homotcomp, funhomotsec.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (free_alg_psfunctor_comp_on_A f g₂ x).
        }
        etrans.
        {
          do 2 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0l.
          }
          apply pathscomp0rid.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          exact (free_alg_psfunctor_cell_on_A _ _).
        }
        refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        apply homotsec_natural'.
    - intros X Y Z f₁ f₂ g τ.
      use free_alg_ump_eq.
      + apply free_alg_is_initial.
      + exact (λ z, free_alg_inc (free_alg Z) (g(f₂ z))).
      + intro x.
        exact (maponpaths
                 (alg_map_carrier (free_alg_psfunctor_mor g))
                 (free_alg_one_cell_on_A
                    (free_alg_is_initial X)
                    (free_alg_psfunctor_obj Y)
                    (λ z, free_alg_inc (free_alg Y) (f₁ z)) x)
               @ free_alg_one_cell_on_A
                   (free_alg_is_initial Y)
                   (free_alg_psfunctor_obj Z)
                   (λ z, free_alg_inc (free_alg Z) (g z))
                   (f₁ x)
               @ maponpaths
                   (free_alg_inc (free_alg Z))
                   (maponpaths g (τ x))).
      + exact (free_alg_one_cell_on_A
                 (free_alg_is_initial X)
                 (free_alg_psfunctor_obj Z)
                 (λ z, free_alg_inc (free_alg Z) (g (f₂ z)))).
      + intro x ; cbn ; unfold homotcomp, homotfun.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (free_alg_psfunctor_cell_on_A _ x).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (free_alg_psfunctor_comp_on_A f₁ g x).
        }
        etrans.
        {
          do 2 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          apply pathsinv0l.
        }
        apply idpath.
      + intro x ; cbn ; unfold homotcomp, homotfun.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (free_alg_psfunctor_comp_on_A f₂ g x).
        }

        etrans.
        {
          do 2 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply pathsinv0l.
          }
          apply pathscomp0rid.
        }
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            refine (!_).
            apply maponpathscomp0.
          }
          etrans.
          {
            apply maponpaths.
            exact (free_alg_psfunctor_cell_on_A _ x).
          }
          apply maponpathscomp0.
        }
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathscomp.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpathscomp.
        }
        refine (!_).
        apply (homotsec_natural'
                 (free_alg_one_cell_on_A
                    (free_alg_is_initial Y)
                    (free_alg_psfunctor_obj Z)
                    (λ z, free_alg_inc (free_alg Z) (g z)))).
  Qed.

  Definition free_alg_psfunctor_invertible_cells
    : invertible_cells free_alg_psfunctor_data.
  Proof.
    split ; intros ; apply hit_alg_is_invertible_2cell_one_type.
  Defined.
  
  Definition free_alg_psfunctor
    : psfunctor one_types (hit_algebra_one_types Σ).
  Proof.
    use make_psfunctor.
    - exact free_alg_psfunctor_data.
    - exact free_alg_psfunctor_laws.
    - exact free_alg_psfunctor_invertible_cells.
  Defined.
End FreeAlgebraFunctor.
