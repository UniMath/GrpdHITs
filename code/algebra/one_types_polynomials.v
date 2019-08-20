(** Interpretation of polynomials in 1-types *)
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
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.

(** Preliminary operations we need *)

(** For coproduct *)
Definition coprodf_path
           {X₁ X₂ Y₁ Y₂ : UU}
           {f₁ g₁ : X₁ → Y₁}
           {f₂ g₂ : X₂ → Y₂}
           (p₁ : f₁ ~ g₁)
           (p₂ : f₂ ~ g₂)
           (x : X₁ ⨿ X₂)
  : coprodf f₁ f₂ x = coprodf g₁ g₂ x.
Proof.
  induction x as [x | x] ; cbn.
  - exact (maponpaths inl (p₁ x)).
  - exact (maponpaths inr (p₂ x)).
Defined.

Definition coprodf_id
           {X Y : UU}
           (x : X ⨿ Y)
  : coprodf (λ z, z) (λ z, z) x = x.
Proof.
  induction x as [x | x].
  - apply idpath.
  - apply idpath.
Defined.

Definition coprodf_comp
           {X₁ X₂ X₃ Y₁ Y₂ Y₃ : UU}
           (f₁ : X₁ → X₂)
           (f₂ : X₂ → X₃)
           (g₁ : Y₁ → Y₂)
           (g₂ : Y₂ → Y₃)
           (x : X₁ ⨿ Y₁)
  : (coprodf (f₂ ∘ f₁) (g₂ ∘ g₁) x
     =
     (coprodf f₂ g₂) (coprodf f₁ g₁ x))%functions.
Proof.
  induction x as [x | x] ; cbn.
  - apply idpath.
  - apply idpath.
Defined.

Definition coprodf_path_maponpaths_inl
           {X₁ X₂ Y₁ Y₂ : UU}
           (f : X₁ → X₂)
           (g : Y₁ → Y₂)
           {x₁ x₂ : X₁}
           (p : x₁ = x₂)
  : maponpaths (coprodf f g) (maponpaths inl p) = maponpaths inl (maponpaths f p).
Proof.
  induction p.
  apply idpath.
Defined.

Definition coprodf_path_maponpaths_inr
           {X₁ X₂ Y₁ Y₂ : UU}
           (f : X₁ → X₂)
           (g : Y₁ → Y₂)
           {y₁ y₂ : Y₁}
           (p : y₁ = y₂)
  : maponpaths (coprodf f g) (maponpaths inr p) = maponpaths inr (maponpaths g p).
Proof.
  induction p.
  apply idpath.
Defined.

(** For products *)
Definition dirprodf_path
           {X₁ X₂ Y₁ Y₂ : UU}
           {f₁ g₁ : X₁ → Y₁}
           {f₂ g₂ : X₂ → Y₂}
           (p₁ : f₁ ~ g₁)
           (p₂ : f₂ ~ g₂)
           (x : X₁ × X₂)
  : dirprodf f₁ f₂ x = dirprodf g₁ g₂ x.
Proof.
  apply pathsdirprod.
  - exact (p₁ (pr1 x)).
  - exact (p₂ (pr2 x)).
Defined.

Definition dirprodf_id
           {X Y : UU}
           (x : X × Y)
  : dirprodf (λ z, z) (λ z, z) x = x.
Proof.
  apply idpath.
Defined.

Definition dirprodf_comp
           {X₁ X₂ X₃ Y₁ Y₂ Y₃ : UU}
           (f₁ : X₁ → X₂)
           (f₂ : X₂ → X₃)
           (g₁ : Y₁ → Y₂)
           (g₂ : Y₂ → Y₃)
           (x : X₁ × Y₁)
  : (dirprodf (f₂ ∘ f₁) (g₂ ∘ g₁) x
     =
     (dirprodf f₂ g₂) (dirprodf f₁ g₁ x))%functions.
Proof.
  apply idpath.
Defined.

Definition pathsdirprod_concat
           {X Y : UU}
           {x₁ x₂ x₃ : X}
           {y₁ y₂ y₃ : Y}
           (p₁ : x₁ = x₂) (p₂ : x₂ = x₃)
           (q₁ : y₁ = y₂) (q₂ : y₂ = y₃)
  : pathsdirprod p₁ q₁ @ pathsdirprod p₂ q₂
    =
    pathsdirprod (p₁ @ p₂) (q₁ @ q₂).
Proof.
  induction p₁, q₁.
  apply idpath.
Defined.

Definition path_dirprodf_path
           {X₁ X₂ Y₁ Y₂ : UU}
           {f₁ g₁ : X₁ → Y₁}
           {f₂ g₂ : X₂ → Y₂}
           {p₁ q₁ : f₁ ~ g₁}
           {p₂ q₂ : f₂ ~ g₂}
           (s₁ : p₁ ~ q₁) (s₂ : p₂ ~ q₂)
           (x : X₁ × X₂)
  : dirprodf_path p₁ p₂ x = dirprodf_path q₁ q₂ x
  := (maponpaths (λ z, pathsdirprod z _) (s₁ (pr1 x)))
       @ maponpaths (λ z, pathsdirprod _ z) (s₂ (pr2 x)).

Definition dirprodf_path_concat
           {X₁ X₂ Y₁ Y₂ : UU}
           {f₁ g₁ h₁ : X₁ → Y₁}
           {f₂ g₂ h₂ : X₂ → Y₂}
           (p₁ : f₁ ~ g₁) (q₁ : g₁ ~ h₁)
           (p₂ : f₂ ~ g₂) (q₂ : g₂ ~ h₂)
           (x : X₁ × X₂)
  : dirprodf_path p₁ p₂ x @ dirprodf_path q₁ q₂ x
    =
    dirprodf_path (homotcomp p₁ q₁) (homotcomp p₂ q₂) x.
Proof.
  apply pathsdirprod_concat.
Defined.

Definition maponpaths_pathsdirprod
           {X₁ X₂ Y₁ Y₂ : UU}
           (φ : X₁ → X₂)
           (χ : Y₁ → Y₂)
           {x₁ x₂ : X₁}
           (p : x₁ = x₂)
           {y₁ y₂ : Y₁}
           (q : y₁ = y₂)
  : pathsdirprod (maponpaths φ p) (maponpaths χ q)
    =
    maponpaths (dirprodf φ χ) (pathsdirprod p q).
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.  

Definition maponpaths_dirprodf_path
           {X₁ X₂ X₃ Y₁ Y₂ Y₃ : UU}
           (φ : X₂ → X₃)
           (χ : Y₂ → Y₃)
           {f₁ g₁ : X₁ → X₂}
           {f₂ g₂ : Y₁ → Y₂}
           (p₁ : f₁ ~ g₁)
           (p₂ : f₂ ~ g₂)
           (x : X₁ × Y₁)
  : dirprodf_path
      (λ (z : X₁), maponpaths φ (p₁ z))
      (λ (z : Y₁), maponpaths χ (p₂ z))
      x
    =
    maponpaths
      (dirprodf φ χ)
      (dirprodf_path p₁ p₂ x)
  := maponpaths_pathsdirprod φ χ (p₁ (pr1 x)) (p₂ (pr2 x)).

(** Action of polynomials on general types *)
Definition poly_homot
           (P : poly_code)
           {X Y : UU}
           {f g : X → Y}
           (p : f ~ g)
  : poly_map P f ~ poly_map P g.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ a, idpath a).
  - exact p.
  - exact (coprodf_path IHP₁ IHP₂).
  - exact (dirprodf_path IHP₁ IHP₂).
Defined.

Definition poly_id
           (P : poly_code)
           (X : UU)
  : (λ x : poly_act P X, x) ~ (poly_map P (λ x : X, x)).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ a, idpath a).
  - exact idpath.
  - intros x.
    refine (!(coprodf_id x) @ _).
    apply coprodf_path.
    + exact IHP₁.
    + exact IHP₂.
  - intros x.
    refine (!(dirprodf_id x) @ _).
    apply dirprodf_path.
    + exact IHP₁.
    + exact IHP₂.
Defined.

Definition poly_comp
           (P : poly_code)
           {X Y Z : UU}
           (f : X → Y) (g : Y → Z)
  : poly_map P g ∘ poly_map P f ~ poly_map P (g ∘ f).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ a, idpath a).
  - exact (λ z, idpath (g(f z))).
  - intro x.
    refine (!(coprodf_comp _ _ _ _ x) @ _).
    apply coprodf_path.
    + exact IHP₁.
    + exact IHP₂.
  - intro x.
    refine (!(dirprodf_comp _ _ _ _ x) @ _).
    apply dirprodf_path.
    + exact IHP₁.
    + exact IHP₂.
Defined.

(** Interpretation of polynomials as pseudofunctors on 1-types *)
Definition poly_act_hlevel
           (P : poly_code)
           (X : one_type)
  : isofhlevel 3 (poly_act P X).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply A.
  - apply X.
  - apply isofhlevelssncoprod.
    + exact IHP₁.
    + exact IHP₂.
  - apply isofhleveldirprod.
    + exact IHP₁.
    + exact IHP₂.
Defined.

Definition sem_poly_one_types_data
           (P : poly_code)
  : psfunctor_data one_types one_types.
Proof.
  use make_psfunctor_data.
  - exact (λ X, make_one_type (poly_act P (X : one_type)) (poly_act_hlevel P X)).
  - exact (λ _ _ f, poly_map P f).
  - exact (λ _ _ _ _ p, poly_homot P p).
  - exact (λ X, poly_id P (X : one_type)).
  - exact (λ _ _ _ f g, poly_comp P f g).
Defined.

Definition sem_poly_one_types_laws
           (P : poly_code)
  : psfunctor_laws (sem_poly_one_types_data P).
Proof.
  repeat split
  ; induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ _ _ _, idpath _).
  - exact (λ _ _ _, idpath _).
  - intros X Y f.
    use funextsec ; intros x.
    induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (eqtohomot (IHP₁ _ _ _) x)).
    + exact (maponpaths (maponpaths inr) (eqtohomot (IHP₂ _ _ _) x)).
  - intros X Y f.
    use funextsec ; intro x.
    exact (path_dirprodf_path
             (eqtohomot (IHP₁ _ _ f))
             (eqtohomot (IHP₂ _ _ f))
             x).
  - exact (λ _ _ _ _ _ _ _, idpath _).
  - exact (λ _ _ _ _ _ _ _, idpath _).
  - intros X Y f g h p q.
    use funextsec ; intro x.
    induction x as [x | x].
    + refine ((maponpaths (maponpaths inl) (eqtohomot (IHP₁ _ _ _ _ _ p q) x))
                @ _).
      apply (maponpathscomp0 inl).
    + refine ((maponpaths (maponpaths inr) (eqtohomot (IHP₂ _ _ _ _ _ p q) x))
                @ _).
      apply (maponpathscomp0 inr).
  - intros X Y f g h p q.
    use funextsec ; intro x.
    refine (_ @ !(dirprodf_path_concat _ _ _ _ _)).
    apply path_dirprodf_path.
    + exact (eqtohomot (IHP₁ _ _ _ _ _ p q)).
    + exact (eqtohomot (IHP₂ _ _ _ _ _ p q)).
  - exact (λ _ _ _, idpath _).
  - exact (λ _ _ _, idpath _).
  - intros X Y f.
    use funextsec ; intro x.
    induction x as [x | x].
    + exact ((maponpaths (maponpaths inl) (eqtohomot (IHP₁ _ _ f) x))
               @ maponpathscomp0 inl _ _
               @ maponpaths (λ p, p @ _) (maponpathscomp0 inl _ _)
               @ maponpaths (λ p, (p @ _) @ _) (!(coprodf_path_maponpaths_inl _ _ _))).
    + exact ((maponpaths (maponpaths inr) (eqtohomot (IHP₂ _ _ f) x))
               @ maponpathscomp0 inr _ _
               @ maponpaths (λ p, p @ _) (maponpathscomp0 inr _ _)
               @ maponpaths (λ p, (p @ _) @ _) (!(coprodf_path_maponpaths_inr _ _ _))).
  - intros X Y f.
    use funextsec.
    intro x.
    refine (path_dirprodf_path
              (eqtohomot (IHP₁ _ _ f))
              (eqtohomot (IHP₂ _ _ f))
              x @ _).
    refine (!(dirprodf_path_concat _ _ _ _ x) @ _).
    refine (maponpaths (λ z, z @ _) _).
    refine (!(dirprodf_path_concat _ _ _ _ x) @ _).
    refine (maponpaths (λ z, z @ _) _).
    exact (maponpaths_dirprodf_path _ _ _ _ x).
  - exact (λ _ _ _, idpath _).
  - exact (λ _ _ _, idpath _).
  - intros X Y f.
    use funextsec ; intro x.
    induction x as [x | x].
    + exact ((maponpaths (maponpaths inl) (eqtohomot (IHP₁ _ _ f) x))
               @ maponpathscomp0 inl _ _
               @ maponpaths (λ p, p @ _) (maponpathscomp0 inl _ _)).
    + exact ((maponpaths (maponpaths inr) (eqtohomot (IHP₂ _ _ f) x))
               @ maponpathscomp0 inr _ _
               @ maponpaths (λ p, p @ _) (maponpathscomp0 inr _ _)).
  - intros X Y f.
    use funextsec ; intro x.
    refine (path_dirprodf_path
              (eqtohomot (IHP₁ _ _ f))
              (eqtohomot (IHP₂ _ _ f))
              x @ _).
    refine (!(dirprodf_path_concat _ _ _ _ x) @ _).
    refine (maponpaths (λ z, z @ _) _).
    exact (!(dirprodf_path_concat _ _ _ _ x)).
  - exact (λ _ _ _ _ _ _ _, idpath _).
  - exact (λ _ _ _ _ _ _ _, idpath _).
  - intros W X Y Z f g h.
    use funextsec ; intro x.
    induction x as [x | x].
    + refine ((maponpaths (λ p, p @ _) (!(maponpathscomp0 inl _ _)))
                @ !(maponpathscomp0 inl _ _)
                @ maponpaths (maponpaths inl) (eqtohomot (IHP₁ _ _ _ _ f g h) x)
                @ maponpathscomp0 inl _ _
                @ maponpaths (λ p, p @ _) (! _)).
      exact (coprodf_path_maponpaths_inl _ _ (poly_comp P₁ f g x)).
    + refine ((maponpaths (λ p, p @ _) (!(maponpathscomp0 inr _ _)))
                @ !(maponpathscomp0 inr _ _)
                @ maponpaths (maponpaths inr) (eqtohomot (IHP₂ _ _ _ _ f g h) x)
                @ maponpathscomp0 inr _ _
                @ maponpaths (λ p, p @ _) (! _)).
      exact (coprodf_path_maponpaths_inr _ _ (poly_comp P₂ f g x)).
  - intros W X Y Z f g h.
    use funextsec ; intro x.
    refine (!_).
    refine (maponpaths (λ p, p @ _) (!_) @ _).
    { exact (maponpaths_dirprodf_path _ _ _ _ x). }
    refine (dirprodf_path_concat _ _ _ _ x @ _).
    refine (!(path_dirprodf_path
                (eqtohomot (IHP₁ _ _ _ _ f g h))
                (eqtohomot (IHP₂ _ _ _ _ f g h))
                x)
             @ _).
    refine (!(dirprodf_path_concat _ _ _ _ x) @ _).
    refine (maponpaths (λ z, z @ _) _).
    exact (!(dirprodf_path_concat _ _ _ _ x)).
  - exact (λ _ _ _ _ _ _ _, idpath _).
  - intros X Y Z f g₁ g₂ p.
    use funextsec ; intro x.
    exact (!(pathscomp0rid _)).
  - intros X Y Z f g₁ g₂ p.
    use funextsec ; intro x.
    induction x as [x | x].
    + exact (!(maponpathscomp0 inl _ _)
              @ maponpaths (maponpaths inl) (eqtohomot (IHP₁ _ _ _ f _ _ p) x)
              @ maponpathscomp0 inl _ _).
    + exact (!(maponpathscomp0 inr _ _)
              @ maponpaths (maponpaths inr) (eqtohomot (IHP₂ _ _ _ f _ _ p) x)
              @ maponpathscomp0 inr _ _).
  - intros X Y Z f g₁ g₂ p.
    use funextsec ; intro x.
    refine ((dirprodf_path_concat _ _ _ _ x)
              @ _).
    refine (path_dirprodf_path
              (eqtohomot (IHP₁ _ _ _ f _ _ p))
              (eqtohomot (IHP₂ _ _ _ f _ _ p))
              x
              @ !_).
    exact (dirprodf_path_concat _ _ _ _ x).
  - exact (λ _ _ _ _ _ _ _, idpath _).
  - intros X Y Z f g₁ g₂ p.
    use funextsec ; intro x.
    exact (!(pathscomp0rid _)).
  - intros X Y Z f₁ f₂ g p.
    use funextsec ; intro x.
    induction x as [x | x].
    + refine (!(maponpathscomp0 inl _ _) @ _).
      refine (_ @ maponpaths (λ p, p @ _) (!(coprodf_path_maponpaths_inl _ _ _))).
      exact (maponpaths (maponpaths inl) (eqtohomot (IHP₁ _ _ _ _ _ g p) x)
                        @ maponpathscomp0 inl _ _).
    + refine (!(maponpathscomp0 inr _ _) @ _).
      refine (_ @ maponpaths (λ p, p @ _) (!(coprodf_path_maponpaths_inr _ _ _))).
      exact (maponpaths (maponpaths inr) (eqtohomot (IHP₂ _ _ _ _ _ g p) x)
                        @ maponpathscomp0 inr _ _).
  - intros X Y Z f₁ f₂ g p.
    use funextsec ; intro x.
    refine ((dirprodf_path_concat _ _ _ _ x)
              @ _).
    refine (path_dirprodf_path
              (eqtohomot (IHP₁ _ _ _ _ _ g p))
              (eqtohomot (IHP₂ _ _ _ _ _ g p))
              x
              @ !_).
    refine (maponpaths (λ z, z @ _) (!_) @ _).
    + exact (maponpaths_dirprodf_path _ _ _ _ x).
    + exact (dirprodf_path_concat _ _ _ _ x).
Qed.

Definition sem_poly_one_types
           (P : poly_code)
  : psfunctor one_types one_types.
Proof.
  use make_psfunctor.
  - exact (sem_poly_one_types_data P).
  - exact (sem_poly_one_types_laws P).
  - split ; intros ; apply one_type_2cell_iso.
Defined.

Notation "⟦ P ⟧" := (sem_poly_one_types P).
