(** The groupoid quotient *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

(** For constant *)
Definition gquot_const
           (A : one_type)
           (X : groupoid)
  : gquot (poly_act_groupoid (C A) X) → A.
Proof.
  use gquot_rec.
  - exact (λ z, z).
  - exact (λ _ _ z, z).
  - exact (λ _, idpath _).
  - exact (λ _ _ _ _ _, idpath _).
  - apply A.
Defined.

(** For identity *)
Definition gquot_id
           (G : groupoid)
  : gquot (poly_act_groupoid I G) → poly_act I (gquot G).
Proof.
  use gquot_rec.
  - exact (gcl G).
  - exact (@gcleq G).
  - exact (ge G).
  - exact (@gconcat G).
  - apply gtrunc.
Defined.

(** For sum *)
Definition gquot_sum
           {P₁ P₂ : poly_code}
           {G : groupoid}
           (IHP₁ : gquot (poly_act_groupoid P₁ G) → poly_act P₁ (gquot G))
           (IHP₂ : gquot (poly_act_groupoid P₂ G) → poly_act P₂ (gquot G))
  : gquot (poly_act_groupoid (P₁ + P₂) G) → poly_act (P₁ + P₂) (gquot G).
Proof.
  use gquot_rec.
  - intro z.
    induction z as [z | z].
    + exact (inl (IHP₁ (gcl (poly_act_groupoid P₁ G) z))).
    + exact (inr (IHP₂ (gcl (poly_act_groupoid P₂ G) z))).
  - intros z₁ z₂ f.
    induction z₁ as [z₁ | z₁], z₂ as [z₂ | z₂].
    + exact (maponpaths (λ z, inl (IHP₁ z)) (gcleq (poly_act_groupoid P₁ G) f)).
    + exact (fromempty f).
    + exact (fromempty f).
    + exact (maponpaths (λ z, inr (IHP₂ z)) (gcleq (poly_act_groupoid P₂ G) f)).
  - intros a.
    induction a as [a | a].
    + exact (maponpaths
               (maponpaths (λ z, inl (IHP₁ z)))
               (ge (poly_act_groupoid P₁ G) a)).
    + exact (maponpaths
               (maponpaths (λ z, inr (IHP₂ z)))
               (ge (poly_act_groupoid P₂ G) a)).
  - intros z₁ z₂ z₃ g₁ g₂.
    induction z₁ as [z₁ | z₁], z₂ as [z₂ | z₂].
    + induction z₃ as [z₃ | z₃].
      * exact (maponpaths
                 (maponpaths (λ z, inl (IHP₁ z)))
                 (gconcat (poly_act_groupoid P₁ G) g₁ g₂)
                 @ maponpathscomp0 _ _ _).
      * exact (fromempty g₂).
    + exact (fromempty g₁).
    + exact (fromempty g₁).
    + induction z₃ as [z₃ | z₃].
      * exact (fromempty g₂).
      * exact (maponpaths
                 (maponpaths (λ z, inr (IHP₂ z)))
                 (gconcat (poly_act_groupoid P₂ G) g₁ g₂)
                 @ maponpathscomp0 _ _ _).
  - apply isofhlevelssncoprod.
    + exact (poly_act_hlevel P₁ (make_one_type (gquot G) (gtrunc G))).
    + exact (poly_act_hlevel P₂ (make_one_type (gquot G) (gtrunc G))).
Defined.

(** For product *)
Definition gquot_prod
           {P₁ P₂ : poly_code}
           {G : groupoid}
           (IHP₁ : gquot (poly_act_groupoid P₁ G) → poly_act P₁ (gquot G))
           (IHP₂ : gquot (poly_act_groupoid P₂ G) → poly_act P₂ (gquot G))
  : gquot (poly_act_groupoid (P₁ * P₂) G) → poly_act (P₁ * P₂) (gquot G).
Proof.
  use gquot_rec.
  - exact (λ z, IHP₁ (gcl (poly_act_groupoid P₁ G) (pr1 z))
                     ,, IHP₂ (gcl (poly_act_groupoid P₂ G) (pr2 z))).
  - exact (λ a₁ a₂ g,
           pathsdirprod
             (maponpaths
                IHP₁
                (gcleq (poly_act_groupoid P₁ G) (pr1 g)))
             (maponpaths
                IHP₂
                (gcleq (poly_act_groupoid P₂ G) (pr2 g)))).
  - exact (λ a,
           maponpaths
             (λ z, pathsdirprod (maponpaths IHP₁ z) _)
             (ge (poly_act_groupoid P₁ G) (pr1 a))
             @ maponpaths
             (λ z, pathsdirprod _ (maponpaths IHP₂ z))
             (ge (poly_act_groupoid P₂ G) (pr2 a))).
  - exact (λ a₁ a₂ a₃ g₁ g₂,
           maponpaths
             (λ z, pathsdirprod (maponpaths IHP₁ z) _)
             (gconcat (poly_act_groupoid P₁ G) (pr1 g₁) (pr1 g₂))
         @ maponpaths
             (λ z, pathsdirprod _ (maponpaths IHP₂ z))
             (gconcat (poly_act_groupoid P₂ G) (pr2 g₁) (pr2 g₂))
         @ maponpaths
             (λ z, pathsdirprod z _)
             (maponpathscomp0 _ _ _)
         @ maponpaths
             (pathsdirprod _)
             (maponpathscomp0 _ _ _)
         @ !(pathsdirprod_concat _ _ _ _)).
  - apply isofhleveldirprod.
    + exact (poly_act_hlevel P₁ (make_one_type (gquot G) (gtrunc G))).
    + exact (poly_act_hlevel P₂ (make_one_type (gquot G) (gtrunc G))).
Defined.

(** Putting it together *)
Definition gquot_poly
           {P : poly_code}
           {G : groupoid}
  : gquot (poly_act_groupoid P G) → poly_act P (gquot G).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (gquot_const A G).
  - exact (gquot_id G).
  - exact (gquot_sum IHP₁ IHP₂).
  - exact (gquot_prod IHP₁ IHP₂).
Defined.
