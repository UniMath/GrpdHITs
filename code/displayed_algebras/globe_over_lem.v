Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import prelude.all.

Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.

Local Open Scope cat.

Definition inv_globe_over
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p q : x₁ = x₂}
           {g : globe p q}
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp : PathOver y₁ y₂ p}
           {qq : PathOver y₁ y₂ q}
           (gg : globe_over Y g pp qq)
  : globe_over Y (! g) qq pp.
Proof.
  induction g ; simpl.
  exact (!gg).
Qed.

Definition inv_globe_over'
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p q : x₁ = x₂}
           {g : globe p q}
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp : PathOver y₁ y₂ p}
           {qq : PathOver y₁ y₂ q}
           (gg : globe_over Y (!g) qq pp)
  : globe_over Y g pp qq.
Proof.
  induction g ; simpl.
  exact (!gg).
Qed.

Definition concat_globe_over
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p q r : x₁ = x₂}
           {g₁ : globe p q}
           {g₂ : globe q r}
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp : PathOver y₁ y₂ p}
           {qq : PathOver y₁ y₂ q}
           {rr : PathOver y₁ y₂ r}
           (gg₁ : globe_over Y g₁ pp qq)
           (gg₂ : globe_over Y g₂ qq rr) 
  : globe_over Y (g₁ @ g₂) pp rr.
Proof.
  induction g₁, g₂.
  exact (gg₁ @ gg₂).
Qed.

Definition globe_over_on_inv
           {X : UU}
           {Y : X → UU}
           {x₂ x₃ : X}
           {q₁ q₂ : x₂ = x₃}
           {y₂ : Y x₂} {y₃ : Y x₃}
           {qq₁ : PathOver y₂ y₃ q₁}
           {qq₂ : PathOver y₂ y₃ q₂}
           {g : globe q₁ q₂}
           (gg : globe_over Y g qq₁ qq₂)
  : globe_over
      Y
      (maponpaths (λ z, ! z) g)
      (inversePathOver qq₁)
      (inversePathOver qq₂).
Proof.
  induction g, q₁.
  exact (maponpaths (λ z, !z) gg).
Qed.

Definition globe_over_compose_left'
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ x₃ : X}
           {p : x₁ = x₂} {q₁ q₂ : x₂ = x₃}
           {y₁ : Y x₁} {y₂ : Y x₂} {y₃ : Y x₃}
           (pp : PathOver y₁ y₂ p)
           {qq₁ : PathOver y₂ y₃ q₁}
           {qq₂ : PathOver y₂ y₃ q₂}
           {g : globe q₁ q₂}
           (gg : globe_over Y g qq₁ qq₂)
  : globe_over
      Y
      (maponpaths (λ z, p @ z) g)
      (composePathOver pp qq₁)
      (composePathOver pp qq₂).
Proof.
  induction g, p, q₁.
  exact (maponpaths (λ z, pp @ z) gg).
Qed.

Definition globe_over_compose_left
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ x₃ x₄ : X}
           {p : x₁ = x₂} {q₁ q₂ : x₂ = x₃} {r : x₃ = x₄}
           {y₁ : Y x₁} {y₂ : Y x₂} {y₄ : Y x₄}
           (pp : PathOver y₁ y₂ p)
           {qq₁ : PathOver y₂ y₄ (q₁ @ r)}
           {qq₂ : PathOver y₂ y₄ (q₂ @ r)}
           {g : globe q₁ q₂}
           (gg : globe_over Y (maponpaths (λ z, z @ r) g) qq₁ qq₂)
  : globe_over
      Y
      (maponpaths (λ (h : x₂ = x₃), p @ (h @ r)) g)
      (composePathOver pp qq₁)
      (composePathOver pp qq₂).
Proof.
  induction g, p, q₁, r.
  exact (maponpaths (λ z, pp @ z) gg).
Qed.

Definition globe_over_compose_right
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ x₃ : X}
           {p₁ p₂ : x₁ = x₂} {q : x₂ = x₃} 
           {y₁ : Y x₁} {y₂ : Y x₂} {y₃ : Y x₃}
           {pp₁ : PathOver y₁ y₂ p₁}
           {pp₂ : PathOver y₁ y₂ p₂}
           (qq : PathOver y₂ y₃ q)
           {g : globe p₁ p₂}
           (gg : globe_over Y g pp₁ pp₂)
  : globe_over
      Y
      (maponpaths (λ h, h @ q) g)
      (composePathOver pp₁ qq)
      (composePathOver pp₂ qq).
Proof.
  induction g, p₁, q.
  exact (maponpaths (λ z, z @ _) gg).
Qed.

Definition globe_over_id_left
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathscomp0lid _)
      (composePathOver
         (identityPathOver _)
         pp)
      pp.
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_id_right
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathscomp0rid _)
      (composePathOver
         pp
         (identityPathOver _))
      pp.
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_inv_left
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathsinv0l _)
      (composePathOver
         (inversePathOver pp)
         pp)
      (identityPathOver _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_inv_right
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathsinv0r _)
      (composePathOver
         pp
         (inversePathOver pp))
      (identityPathOver _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_assocl
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ x₃ x₄ : X}
           {p₁ : x₁ = x₂} {p₂ : x₂ = x₃} {p₃ : x₃ = x₄}
           {y₁ : Y x₁} {y₂ : Y x₂} {y₃ : Y x₃} {y₄ : Y x₄}
           (pp₁ : PathOver y₁ y₂ p₁)
           (pp₂ : PathOver y₂ y₃ p₂)
           (pp₃ : PathOver y₃ y₄ p₃)
  : globe_over
      Y
      (path_assoc _ _ _)
      (composePathOver pp₁ (composePathOver pp₂ pp₃))
      (composePathOver (composePathOver pp₁ pp₂) pp₃).
Proof.
  induction p₁, p₂, p₃, pp₁, pp₂, pp₃.
  apply idpath.
Qed.

Definition globe_over_assocr
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ x₃ x₄ : X}
           {p₁ : x₁ = x₂} {p₂ : x₂ = x₃} {p₃ : x₃ = x₄}
           {y₁ : Y x₁} {y₂ : Y x₂} {y₃ : Y x₃} {y₄ : Y x₄}
           (pp₁ : PathOver y₁ y₂ p₁)
           (pp₂ : PathOver y₂ y₃ p₂)
           (pp₃ : PathOver y₃ y₄ p₃)
  : globe_over
      Y
      (!(path_assoc _ _ _))
      (composePathOver (composePathOver pp₁ pp₂) pp₃)
      (composePathOver pp₁ (composePathOver pp₂ pp₃)).
Proof.
  induction p₁, p₂, p₃, pp₁, pp₂, pp₃.
  apply idpath.
Qed.

Definition globe_over_inv_inv
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      Y
      (pathsinv0inv0 p)
      (inversePathOver (inversePathOver pp))
      pp.
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_comp_inv
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ x₃ : X}
           {p : x₁ = x₂} {q : x₂ = x₃}
           {y₁ : Y x₁} {y₂ : Y x₂} {y₃ : Y x₃}
           (pp : PathOver y₁ y₂ p)
           (qq : PathOver y₂ y₃ q)
  : globe_over
      Y
      (pathscomp_inv _ _)
      (inversePathOver (composePathOver pp qq))
      (composePathOver (inversePathOver qq) (inversePathOver pp)).
Proof.
  induction p, pp, q, qq.
  apply idpath.
Qed.

Definition globe_over_move_globe
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p₁ p₂ : x₁ = x₂} 
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp₁ : PathOver y₁ y₂ p₁}
           {pp₂ : PathOver y₁ y₂ p₂}
           {g₁ g₂ : globe p₁ p₂}
           (h : g₁ = g₂)
           (gg : globe_over Y g₁ pp₁ pp₂)
  : globe_over Y g₂ pp₁ pp₂.
Proof.
  induction h.
  exact gg.
Qed.

Definition globe_over_move_globe_one_type
           {X : UU}
           (HX : isofhlevel 3 X)
           {Y : X → UU}
           {x₁ x₂ : X}
           {p₁ p₂ : x₁ = x₂} 
           {y₁ : Y x₁} {y₂ : Y x₂}
           {pp₁ : PathOver y₁ y₂ p₁}
           {pp₂ : PathOver y₁ y₂ p₂}
           {g₁ g₂ : globe p₁ p₂}
           (gg : globe_over Y g₁ pp₁ pp₂)
  : globe_over Y g₂ pp₁ pp₂.
Proof.
  use globe_over_move_globe.
  - exact g₁.
  - exact (pr1 (HX x₁ x₂ p₁ p₂ g₁ g₂)).
  - exact gg.    
Qed.

Definition TotalPathToPathOver
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : x = y)
  : PathOver (pr2 x) (pr2 y) (maponpaths pr1 p).
Proof.
  induction p ; cbn.
  apply idpath.
Defined.

Definition PathOverToTotalPath'
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : pr1 x = pr1 y)
           (q : PathOver (pr2 x) (pr2 y) p)
  : x = y.
Proof.
  use PathOverToTotalPath.
  - exact p.
  - exact q.
Defined.

Definition globe_over_to_homot
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           {p₁ p₂ : pr1 x = pr1 y}
           (q₁ : PathOver (pr2 x) (pr2 y) p₁)
           (q₂ : PathOver (pr2 x) (pr2 y) p₂)
           (g : globe p₁ p₂)
           (gg : globe_over Y g q₁ q₂)
  : PathOverToTotalPath' _ q₁ = PathOverToTotalPath' _ q₂.
Proof.
  induction g ; simpl in *.
  unfold globe_over in gg.
  cbn in gg.
  unfold idfun in gg.
  apply maponpaths.
  refine (_ @ maponpaths path_to_PathOver gg @ _).
  - exact (!(homotinvweqweq (make_weq _ (PathOver_to_path_isweq _ _ _)) q₁)).
  - exact (homotinvweqweq (make_weq _ (PathOver_to_path_isweq _ _ _)) q₂).
Defined.

Definition path_is_PathOverToTotalPath'
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : x = y)
  : p
    =
    PathOverToTotalPath'
      _
      (TotalPathToPathOver p).
Proof.
  induction p.
  apply idpath.
Defined.
  
Definition maponpaths_pr1_PathOverToTotalPath
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ : Y x₁} {y₂ : Y x₂}
           (q : PathOver y₁ y₂ p)
  : maponpaths pr1 (PathOverToTotalPath q)
    =
    p.
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.

Definition maponpaths_pr1_PathOverToTotalPath'
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : pr1 x = pr1 y)
           (q : PathOver (pr2 x) (pr2 y) p)
  : maponpaths pr1 (PathOverToTotalPath' p q)
    =
    p.
Proof.
  induction x as [x₁ x₂], y as [y₁ y₂].
  simpl in *.
  induction p.
  induction q.
  apply idpath.
Defined.

Definition TotalPathToPathOver_PathOverToTotalPath'
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (x : X), Y x}
           (p : pr1 x = pr1 y)
           (q : PathOver (pr2 x) (pr2 y) p)
  : globe_over
      Y
      (maponpaths_pr1_PathOverToTotalPath' p q)
      (TotalPathToPathOver (PathOverToTotalPath' p q))
      q.
Proof.
  induction x as [x₁ x₂], y as [y₁ y₂] ; simpl in *.
  induction p, q.
  apply idpath.
Qed.


Definition globe_over_pr1
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ y₁ : poly_act P₁ X} {x₂ y₂ : poly_act P₂ X}
           {p q : x₁ ,, x₂ = y₁ ,, y₂}
           {g₁ : p = q}
           {z₁ : poly_dact_UU (P₁ * P₂) Y (x₁ ,, x₂)}
           {z₂ : poly_dact_UU (P₁ * P₂) Y (y₁ ,, y₂)}
           {pp : PathOver z₁ z₂ p}
           {pp' : PathOver z₁ z₂ q}
           (gg : globe_over
                   (poly_dact_UU (P₁ * P₂) Y)
                   g₁
                   pp
                   pp')
  : globe_over
      (poly_dact_UU P₁ Y)
      (maponpaths (maponpaths pr1) g₁)
      (PathOver_pr1 pp)
      (PathOver_pr1 pp').
Proof.
  induction g₁, p.
  unfold globe in *.
  induction pp ; simpl in *.
  use globe_over_move_globe_one_type.
  { apply (⟦ P₁ ⟧ _). }
  { apply idpath. }
  simpl.
  unfold globe_over in *.
  cbn in * ; unfold idfun in * ; cbn in *.
  rewrite <- gg.
  apply idpath.
Qed.

Definition globe_over_pr2
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ y₁ : poly_act P₁ X} {x₂ y₂ : poly_act P₂ X}
           {p q : x₁ ,, x₂ = y₁ ,, y₂}
           {g₁ : p = q}
           {z₁ : poly_dact_UU (P₁ * P₂) Y (x₁ ,, x₂)}
           {z₂ : poly_dact_UU (P₁ * P₂) Y (y₁ ,, y₂)}
           {pp : PathOver z₁ z₂ p}
           {pp' : PathOver z₁ z₂ q}
           (gg : globe_over
                   (poly_dact_UU (P₁ * P₂) Y)
                   g₁
                   pp
                   pp')
  : globe_over
      (poly_dact_UU P₂ Y)
      (maponpaths (maponpaths dirprod_pr2) g₁)
      (PathOver_pr2 pp)
      (PathOver_pr2 pp').
Proof.
  induction g₁, p.
  unfold globe in *.
  induction pp ; simpl in *.
  use globe_over_move_globe_one_type.
  { apply (⟦ P₂ ⟧ _). }
  { apply idpath. }
  simpl.
  unfold globe_over in *.
  cbn in * ; unfold idfun in * ; cbn in *.
  rewrite <- gg.
  apply idpath.
Qed.

Definition PathOver_pr1_concat
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ x₃ : poly_act (P₁ * P₂) X}
           {y₁ : poly_dact_UU (P₁ * P₂) Y x₁}
           {y₂ : poly_dact_UU (P₁ * P₂) Y x₂}
           {y₃ : poly_dact_UU (P₁ * P₂) Y x₃}
           {p₁ : x₁ = x₂} {p₂ : x₂ = x₃}
           (pp₁ : PathOver y₁ y₂ p₁)
           (pp₂ : PathOver y₂ y₃ p₂)
  : globe_over
      (poly_dact P₁ Y)
      (maponpathscomp0 _ _ _)
      (PathOver_pr1 (composePathOver pp₁ pp₂))
      (composePathOver (PathOver_pr1 pp₁) (PathOver_pr1 pp₂)).
Proof.
  induction p₁, p₂, pp₁, pp₂.
  apply idpath.
Qed.

Definition PathOver_pr1_inv
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act (P₁ * P₂) X}
           {y₁ : poly_dact_UU (P₁ * P₂) Y x₁}
           {y₂ : poly_dact_UU (P₁ * P₂) Y x₂}
           {p : x₁ = x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      (poly_dact P₁ Y)
      (maponpathsinv0 _ _)
      (PathOver_pr1 (inversePathOver pp))
      (inversePathOver (PathOver_pr1 pp)).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_pr1_pair
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ X} {y₁ y₂ : poly_act P₂ X}
           {z₁ : poly_dact_UU P₁ Y x₁}
           {z₂ : poly_dact_UU P₁ Y x₂}
           {z₁' : poly_dact_UU P₂ Y y₁}
           {z₂' : poly_dact_UU P₂ Y y₂}
           {p : x₁ = x₂} {q : y₁ = y₂}
           (pp : PathOver z₁ z₂ p)
           (qq : PathOver z₁' z₂' q)
  : globe_over
      (poly_dact P₁ Y)
      (maponpaths_pr1_pathsdirprod _ _)
      (PathOver_pr1 (PathOver_pair pp qq))
      pp.
Proof.
  induction p, q, pp, qq.
  apply idpath.
Qed.

Definition PathOver_pr2_concat
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ x₃ : poly_act (P₁ * P₂) X}
           {y₁ : poly_dact_UU (P₁ * P₂) Y x₁}
           {y₂ : poly_dact_UU (P₁ * P₂) Y x₂}
           {y₃ : poly_dact_UU (P₁ * P₂) Y x₃}
           {p₁ : x₁ = x₂} {p₂ : x₂ = x₃}
           (pp₁ : PathOver y₁ y₂ p₁)
           (pp₂ : PathOver y₂ y₃ p₂)
  : globe_over
      (poly_dact P₂ Y)
      (maponpathscomp0 _ _ _)
      (PathOver_pr2 (composePathOver pp₁ pp₂))
      (composePathOver (PathOver_pr2 pp₁) (PathOver_pr2 pp₂)).
Proof.
  induction p₁, p₂, pp₁, pp₂.
  apply idpath.
Qed.

Definition PathOver_pr2_inv
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act (P₁ * P₂) X}
           {y₁ : poly_dact_UU (P₁ * P₂) Y x₁}
           {y₂ : poly_dact_UU (P₁ * P₂) Y x₂}
           {p : x₁ = x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      (poly_dact P₂ Y)
      (maponpathsinv0 _ _)
      (PathOver_pr2 (inversePathOver pp))
      (inversePathOver (PathOver_pr2 pp)).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_pr2_pair
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ X} {y₁ y₂ : poly_act P₂ X}
           {z₁ : poly_dact_UU P₁ Y x₁}
           {z₂ : poly_dact_UU P₁ Y x₂}
           {z₁' : poly_dact_UU P₂ Y y₁}
           {z₂' : poly_dact_UU P₂ Y y₂}
           {p : x₁ = x₂} {q : y₁ = y₂}
           (pp : PathOver z₁ z₂ p)
           (qq : PathOver z₁' z₂' q)
  : globe_over
      (poly_dact P₂ Y)
      (maponpaths_pr2_pathsdirprod _ _)
      (PathOver_pr2 (PathOver_pair pp qq))
      qq.
Proof.
  induction p, q, pp, qq.
  apply idpath.
Qed.

Definition globe_over_inl
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x y : poly_act P₁ X}
           {p q : x = y}
           {g₁ : p = q}
           {z₁ : poly_dact_UU P₁ Y x}
           {z₂ : poly_dact_UU P₁ Y y}
           {pp : PathOver z₁ z₂ p}
           {pp' : PathOver z₁ z₂ q}
           (gg : globe_over
                   (poly_dact_UU P₁ Y)
                   g₁
                   pp
                   pp')
  : globe_over
      (poly_dact_UU (P₁ + P₂) Y)
      (maponpaths (maponpaths inl) g₁)
      (PathOver_inl pp)
      (PathOver_inl pp').
Proof.
  induction g₁, p.
  unfold globe in *.
  induction pp ; simpl in *.
  use globe_over_move_globe_one_type.
  { apply (⟦ P₁ + P₂ ⟧ _). }
  { apply idpath. }
  simpl.
  unfold globe_over in *.
  cbn in * ; unfold idfun in * ; cbn in *.
  exact gg.
Qed.

Definition PathOver_inl_concat
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ x₃ : poly_act P₁ X}
           {y₁ : poly_dact_UU P₁ Y x₁}
           {y₂ : poly_dact_UU P₁ Y x₂}
           {y₃ : poly_dact_UU P₁ Y x₃}
           {p₁ : x₁ = x₂} {p₂ : x₂ = x₃}
           (pp₁ : PathOver y₁ y₂ p₁)
           (pp₂ : PathOver y₂ y₃ p₂)
  : globe_over
      (poly_dact (P₁ + P₂) Y)
      (maponpathscomp0 inl p₁ p₂)
      (PathOver_inl (composePathOver pp₁ pp₂))
      (composePathOver (PathOver_inl pp₁) (PathOver_inl pp₂)).
Proof.
  induction p₁, p₂, pp₁, pp₂.
  apply idpath.
Qed.

Definition PathOver_inl_inv
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ X}
           {y₁ : poly_dact_UU P₁ Y x₁}
           {y₂ : poly_dact_UU P₁ Y x₂}
           {p : x₁ = x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      (poly_dact (P₁ + P₂) Y)
      (maponpathsinv0 inl p)
      (PathOver_inl (inversePathOver pp))
      (inversePathOver (PathOver_inl pp)).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition globe_over_inr
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x y : poly_act P₂ X}
           {p q : x = y}
           {g₁ : p = q}
           {z₁ : poly_dact_UU P₂ Y x}
           {z₂ : poly_dact_UU P₂ Y y}
           {pp : PathOver z₁ z₂ p}
           {pp' : PathOver z₁ z₂ q}
           (gg : globe_over
                   (poly_dact_UU P₂ Y)
                   g₁
                   pp
                   pp')
  : globe_over
      (poly_dact_UU (P₁ + P₂) Y)
      (maponpaths (maponpaths inr) g₁)
      (PathOver_inr pp)
      (PathOver_inr pp').
Proof.
  induction g₁, p.
  unfold globe in *.
  induction pp ; simpl in *.
  use globe_over_move_globe_one_type.
  { apply (⟦ P₁ + P₂ ⟧ _). }
  { apply idpath. }
  simpl.
  unfold globe_over in *.
  cbn in * ; unfold idfun in * ; cbn in *.
  exact gg.
Qed.

Definition PathOver_inr_concat
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ x₃ : poly_act P₂ X}
           {y₁ : poly_dact_UU P₂ Y x₁}
           {y₂ : poly_dact_UU P₂ Y x₂}
           {y₃ : poly_dact_UU P₂ Y x₃}
           {p₁ : x₁ = x₂} {p₂ : x₂ = x₃}
           (pp₁ : PathOver y₁ y₂ p₁)
           (pp₂ : PathOver y₂ y₃ p₂)
  : globe_over
      (poly_dact (P₁ + P₂) Y)
      (maponpathscomp0 inr p₁ p₂)
      (PathOver_inr (composePathOver pp₁ pp₂))
      (composePathOver (PathOver_inr pp₁) (PathOver_inr pp₂)).
Proof.
  induction p₁, p₂, pp₁, pp₂.
  apply idpath.
Qed.

Definition PathOver_inr_inv
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₂ X}
           {y₁ : poly_dact_UU P₂ Y x₁}
           {y₂ : poly_dact_UU P₂ Y x₂}
           {p : x₁ = x₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      (poly_dact (P₁ + P₂) Y)
      (maponpathsinv0 inr p)
      (PathOver_inr (inversePathOver pp))
      (inversePathOver (PathOver_inr pp)).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition apd2_idfun
           {A : UU}
           {YA : A → UU}
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {y₁ : YA a₁} {y₂ : YA a₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      YA
      (maponpathsidfun p)
      (apd_2 (λ (a : A) (y : YA a), y) p pp)
      pp.
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition apd2_concat
           {A B : UU}
           {YA : A → UU} {YB : B → UU}
           {f : A → B}
           (ff : ∏ (a : A), YA a → YB (f a))
           {a₁ a₂ a₃ : A}
           {p : a₁ = a₂} {q : a₂ = a₃}
           {y₁ : YA a₁} {y₂ : YA a₂} {y₃ : YA a₃}
           (pp : PathOver y₁ y₂ p)
           (qq : PathOver y₂ y₃ q)
  : globe_over
      YB
      (maponpathscomp0 f p q)
      (apd_2 ff (p @ q) (composePathOver pp qq))
      (composePathOver
         (apd_2 ff p pp)
         (apd_2 ff q qq)).
Proof.
  induction p, pp, q, qq.
  apply idpath.
Qed.

Definition apd2_inv
           {A B : UU}
           {YA : A → UU} {YB : B → UU}
           {f : A → B}
           (ff : ∏ (a : A), YA a → YB (f a))
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {y₁ : YA a₁} {y₂ : YA a₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      YB
      (!(maponpathsinv0 f p))
      (inversePathOver (apd_2 ff _ pp))
      (apd_2 ff _ (inversePathOver pp)).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition apd2_comp
           {A B C : UU}
           {YA : A → UU} {YB : B → UU} {YC : C → UU}
           {f : A → B} {g : B → C}
           (ff : ∏ (a : A), YA a → YB (f a))
           (gg : ∏ (b : B), YB b → YC (g b))
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {y₁ : YA a₁} {y₂ : YA a₂}
           (pp : PathOver y₁ y₂ p)
  : globe_over
      YC
      (maponpathscomp f g p)
      (apd_2 gg (maponpaths f p) (apd_2 ff p pp))
      (apd_2 (λ a z, gg (f a) (ff a z)) p pp).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition apd2_globe_over
           {A B : UU}
           {YA : A → UU} {YB : B → UU} 
           {f : A → B}
           (ff : ∏ (a : A), YA a → YB (f a))
           {a₁ a₂ : A}
           {p p' : a₁ = a₂}
           {g : globe p p'}
           {y₁ : YA a₁} {y₂ : YA a₂}
           {pp : PathOver y₁ y₂ p} {pp' : PathOver y₁ y₂ p'}
           (gg : globe_over YA g pp pp')
  : globe_over
      YB
      (maponpaths (maponpaths f) g)
      (apd_2 ff _ pp)
      (apd_2 ff _ pp').
Proof.
  induction g, p, pp.
  exact (!(maponpaths _ (!gg))).
Qed.

Definition apd2_inl
           {P Q : poly_code}
           {A : one_type}
           {YA : A → one_type}
           {a₁ a₂ : poly_act P A}
           {p : a₁ = a₂}
           {y₁ : poly_dact P YA a₁} {y₂ : poly_dact P YA a₂}
           (pp : @PathOver _ _ _ (poly_dact P YA) y₁ y₂ p)
  : globe_over
      (poly_dact (P + Q) YA)
      (idpath _)
      (@apd_2
         _ _
         (poly_dact P YA)
         (poly_dact (P + Q) YA)
         inl
         (λ _ z, z)
         _ _ _ _ _
         pp)
      (PathOver_inl pp).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition apd2_inr
           {P Q : poly_code}
           {A : one_type}
           {YA : A → one_type}
           {a₁ a₂ : poly_act Q A}
           {p : a₁ = a₂}
           {y₁ : poly_dact Q YA a₁} {y₂ : poly_dact Q YA a₂}
           (pp : @PathOver _ _ _ (poly_dact Q YA) y₁ y₂ p)
  : globe_over
      (poly_dact (P + Q) YA)
      (idpath _)
      (@apd_2
         _ _
         (poly_dact Q YA)
         (poly_dact (P + Q) YA)
         inr
         (λ _ z, z)
         _ _ _ _ _
         pp)
      (PathOver_inr pp).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_pair_concat
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ x₃ : poly_act P₁ X}
           {x₁' x₂' x₃' : poly_act P₂ X}
           {y₁ : poly_dact_UU P₁ Y x₁}
           {y₂ : poly_dact_UU P₁ Y x₂}
           {y₃ : poly_dact_UU P₁ Y x₃}
           {y₁' : poly_dact_UU P₂ Y x₁'}
           {y₂' : poly_dact_UU P₂ Y x₂'}
           {y₃' : poly_dact_UU P₂ Y x₃'}
           {p₁ : x₁ = x₂} {p₂ : x₂ = x₃}
           {q₁ : x₁' = x₂'} {q₂ : x₂' = x₃'}
           (pp₁ : PathOver y₁ y₂ p₁)
           (pp₂ : PathOver y₂ y₃ p₂)
           (qq₁ : PathOver y₁' y₂' q₁)
           (qq₂ : PathOver y₂' y₃' q₂)
  : globe_over
      (poly_dact (P₁ * P₂) Y)
      (!(pathsdirprod_concat _ _ _ _))
      (PathOver_pair
         (composePathOver pp₁ pp₂)
         (composePathOver qq₁ qq₂))
      (composePathOver
         (PathOver_pair pp₁ qq₁)
         (PathOver_pair pp₂ qq₂)).
Proof.
  induction p₁, p₂, q₁, q₂, pp₁, pp₂, qq₁, qq₂.
  apply idpath.
Qed.

Definition PathOver_pair_inv
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ X}
           {x₁' x₂' : poly_act P₂ X}
           {y₁ : poly_dact_UU P₁ Y x₁}
           {y₂ : poly_dact_UU P₁ Y x₂}
           {y₁' : poly_dact_UU P₂ Y x₁'}
           {y₂' : poly_dact_UU P₂ Y x₂'}
           {p : x₁ = x₂}
           {q : x₁' = x₂'}
           (pp : PathOver y₁ y₂ p)
           (qq : PathOver y₁' y₂' q)
  : globe_over
      (poly_dact (P₁ * P₂) Y)
      (!(pathsdirprod_inv _ _))
      (PathOver_pair (inversePathOver pp) (inversePathOver qq))
      (inversePathOver (PathOver_pair pp qq)).
Proof.
  induction p, q, pp, qq.
  apply idpath.
Qed.

Definition globe_over_PathOver_pair
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ X}
           {x₁' x₂' : poly_act P₂ X}
           {y₁ : poly_dact_UU P₁ Y x₁}
           {y₂ : poly_dact_UU P₁ Y x₂}
           {y₁' : poly_dact_UU P₂ Y x₁'}
           {y₂' : poly_dact_UU P₂ Y x₂'}
           {p p' : x₁ = x₂}
           {q q' : x₁' = x₂'}
           {pp : PathOver y₁ y₂ p}
           {pp' : PathOver y₁ y₂ p'}
           {g₁ : globe p p'}
           (gg₁ : globe_over (poly_dact P₁ Y) g₁ pp pp')
           {qq : PathOver y₁' y₂' q}
           {qq' : PathOver y₁' y₂' q'}
           {g₂ : globe q q'}
           (gg₂ : globe_over (poly_dact P₂ Y) g₂ qq qq')
  : globe_over
      (poly_dact (P₁ * P₂) Y)
      (paths_pathsdirprod g₁ g₂)
      (PathOver_pair pp qq)
      (PathOver_pair pp' qq').
Proof.
  induction g₁, p, g₂, q.
  exact (paths_pathsdirprod gg₁ gg₂).
Qed.

Definition PathOver_natural
           {A B : UU}
           (HB : isofhlevel 3 B)
           {YA : A → UU} {YB : B → UU}
           {f g : A → B}
           {ff : ∏ (a : A), YA a → YB (f a)}
           {gg : ∏ (a : A), YA a → YB (g a)}
           {p : f ~ g}
           (pp : ∏ (a : A) (y : YA a),
                 PathOver (ff a y) (gg a y) (p a))
           {a b : A}
           {ya : YA a} {yb : YA b}
           {q : a = b}
           (qq : PathOver ya yb q)
  : globe_over
      YB
      (maponpaths (λ z, (z @ _) @ _) (!(maponpathsinv0 f q))
       @ !(path_assoc _ _ _)
       @ !(homotsec_natural p q))
      (composePathOver
         (composePathOver
            (inversePathOver (apd_2 ff q qq))
            (pp a ya))
         (apd_2 gg q qq))
      (pp b yb).
Proof.
  induction q, qq.
  refine (globe_over_move_globe_one_type _ _).
  { apply HB. }
  exact (concat_globe_over
           (globe_over_id_right _)
           (globe_over_id_left _)).
Qed.
