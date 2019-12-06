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

Definition total2_one_type
           {X : one_type}
           (Y : X → one_type)
  : one_type.
Proof.
  use make_one_type.
  - exact (total2 Y).
  - use isofhleveltotal2.
    + apply X.
    + intro ; apply Y.
Defined.

(**
We first look at the first and second projection of a polynomial applied to a total type
 *)
Definition poly_pr1
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
  : poly_act P (total2_one_type Y) → poly_act P X
  := poly_map P pr1.

Definition poly_pr2
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
  : ∏ (x : poly_act P (total2_one_type Y)), poly_dact P Y (poly_pr1 P x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl in *.
  - exact (λ x, x).
  - exact (λ x, pr2 x).
  - induction x as [x | x] ; simpl.
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - intros x.
    refine (_ ,, _).
    + exact (IHP₁ (pr1 x)).
    + exact (IHP₂ (pr2 x)).
Defined.

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

Definition PathOver_poly_pr2
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
           {x y : poly_act P (∑ z, Y z)}
           (p : x = y)
  : @PathOver
      _ _ _
      (poly_dact P Y)
      (poly_pr2 P x)
      (poly_pr2 P y)
      (maponpaths (poly_pr1 _) p).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl in *.
  - induction p.
    apply idpath.
  - apply TotalPathToPathOver.
  - induction p ; apply idpath.
  - induction p ; apply idpath.
Defined.

Definition PathOver_poly_pr2_is_idpath
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
           (x : poly_act P (∑ z, Y z))
  : PathOver_poly_pr2 P (idpath x) = idpath _.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; apply idpath.
Qed.

Definition PathOver_poly_pr2_is_idpath_globe
           (P : poly_code)
           {X : one_type}
           {Y : X → one_type}
           (x : poly_act P (∑ z, Y z))
  : globe_over
      (poly_dact P Y)
      (idpath _)
      (PathOver_poly_pr2 P (idpath x))
      (identityPathOver _).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; apply idpath.
Qed.

Definition PathOver_pr1_PathOver_poly_pr2
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {z₁ z₂ : poly_act (P₁ * P₂) (∑ z : X, Y z)}
           (p : z₁ = z₂)
  : globe_over
      (poly_dact _ Y)
      (maponpathscomp pr1 (poly_map P₁ pr1) p
       @ !(maponpathscomp (dirprodf (poly_map P₁ pr1) (poly_map P₂ pr1)) pr1 p))
      (PathOver_poly_pr2 P₁ (maponpaths pr1 p))
      (PathOver_pr1 (PathOver_poly_pr2 (P₁ * P₂) p)).
Proof.
  induction p.
  exact (PathOver_poly_pr2_is_idpath _ _).
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

Definition PathOver_pr2_PathOver_poly_pr2
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {z₁ z₂ : poly_act (P₁ * P₂) (∑ z : X, Y z)}
           (p : z₁ = z₂)
  : globe_over
      (poly_dact _ Y)
      (maponpathscomp dirprod_pr2 (poly_pr1 P₂) p
       @ !(maponpathscomp (poly_pr1 (P₁ * P₂)) dirprod_pr2 p))
      (PathOver_poly_pr2 P₂ (maponpaths dirprod_pr2 p))
      (PathOver_pr2 (PathOver_poly_pr2 (P₁ * P₂) p)).
Proof.
  induction p.
  exact (PathOver_poly_pr2_is_idpath _ _).
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

Definition PathOver_pr1_PathOver_poly_inl
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {z₁ z₂ : poly_act P₁ (∑ z : X, Y z)}
           (p : z₁ = z₂)
  : globe_over
      (poly_dact (P₁ + P₂) Y)
      (coprodf_path_maponpaths_inl (poly_pr1 P₁) (poly_pr1 P₂) p)
      (PathOver_poly_pr2 (P₁ + P₂) (maponpaths inl p))
      (PathOver_inl (PathOver_poly_pr2 P₁ p)).
Proof.
  induction p.
  exact (!(PathOver_poly_pr2_is_idpath _ _)).
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

Definition PathOver_pr1_PathOver_poly_inr
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {z₁ z₂ : poly_act P₂ (∑ z : X, Y z)}
           (p : z₁ = z₂)
  : globe_over
      (poly_dact (P₁ + P₂) Y)
      (coprodf_path_maponpaths_inr (poly_pr1 P₁) (poly_pr1 P₂) p)
      (PathOver_poly_pr2 (P₁ + P₂) (maponpaths inr p))
      (PathOver_inr (PathOver_poly_pr2 P₂ p)).
Proof.
  induction p.
  exact (!(PathOver_poly_pr2_is_idpath _ _)).
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

Definition PathOver_pr1_PathOver_poly_inv
           {P : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x y : poly_act P (∑ z : X, Y z)}
           (p : x = y)
  : globe_over
      (poly_dact P Y)
      (maponpathsinv0 _ _)
      (PathOver_poly_pr2 P (!p))
      (inversePathOver (PathOver_poly_pr2 P p)).
Proof.
  induction p.
  induction P ; apply idpath.
Qed.

Definition PathOver_pr1_PathOver_poly_concat
           {P : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x y z : poly_act P (∑ z : X, Y z)}
           (p : x = y) (q : y = z)
  : globe_over
      (poly_dact P Y)
      (maponpathscomp0 (poly_pr1 P) p q)
      (PathOver_poly_pr2 P (p @ q))
      (composePathOver
         (PathOver_poly_pr2 P p)
         (PathOver_poly_pr2 P q)).
Proof.
  induction p, q.
  unfold globe_over.
  simpl.
  cbn.
  unfold idfun.
  refine (!(pathscomp0rid _) @ !_).
  apply maponpaths.
  exact (PathOver_poly_pr2_is_idpath _ _).
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

Definition PathOver_pr2_PathOver_pair
           {P₁ P₂ : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {x₁ x₂ : poly_act P₁ (∑ z : X, Y z)}
           {y₁ y₂ : poly_act P₂ (∑ z : X, Y z)}
           (p : x₁ = x₂) (q : y₁ = y₂)
  : globe_over
      (poly_dact (P₁ * P₂) Y)
      (!(maponpaths_pathsdirprod _ _ _ _))
      (PathOver_poly_pr2 (P₁ * P₂) (pathsdirprod p q))
      (PathOver_pair
         (PathOver_poly_pr2 P₁ p)
         (PathOver_poly_pr2 P₂ q)).
Proof.
  induction p, q.
  exact (!(paths_pathsdirprod
             (PathOver_poly_pr2_is_idpath _ _)
             (PathOver_poly_pr2_is_idpath _ _))).
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

(**
Now we define the total algebra
 *)
Section TotalAlgebra.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}.
  Variable (Y : disp_algebra X).

  Local Definition carrier
    : one_type
    := total2_one_type (pr1 Y).

  Local Definition operation
    : poly_act (point_constr Σ) carrier → carrier
    := λ x,
       ((alg_constr X (poly_pr1 (point_constr Σ) x))
          ,,
          disp_alg_constr Y (poly_pr1 (point_constr Σ) x) (poly_pr2 (point_constr Σ) x)).

  Local Definition total_prealgebra
    : hit_prealgebra_one_types Σ.
  Proof.
    use tpair.
    - exact carrier.
    - exact operation.
  Defined.

  (** For the paths, we first need to look at the first and second projections of endpoints *)
  Local Definition pr1_endpoint
        {P Q : poly_code}
        (e : endpoint (point_constr Σ) P Q)
        (x : poly_act P carrier)
    : sem_endpoint_UU e (alg_constr X) (poly_pr1 P x)
      =
      poly_pr1 Q (sem_endpoint_UU e operation x).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ]
    ; try (apply idpath).
    - exact (maponpaths _ (IHe₁ _) @ IHe₂ _).
    - exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  Defined.

  Local Definition pr2_endpoint
        {P Q : poly_code}
        (e : endpoint (point_constr Σ) P Q)
        (x : poly_act P carrier)
    : @PathOver
        _ _ _
        (poly_dact Q (pr1 Y))
        (endpoint_dact _ _ e (disp_alg_constr Y) (poly_pr2 P x))
        (poly_pr2 Q (sem_endpoint_UU e operation x))
        (pr1_endpoint e _).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ].
    - apply idpath.
    - simpl.
      refine
        (composePathOver
           _
           (IHe₂ _)).
      exact (@apd_2
              _
              (poly_act R (path_alg_carrier (pr1 X)))
              _
              (poly_dact R (pr1 Y))
              _
              (λ _, endpoint_dact (pr11 X) (pr1 Y) e₂ (disp_alg_constr Y))
              _ _
              _
              _ _
              (IHe₁ x)
            ).
    - apply idpath.
    - apply idpath.
    - apply idpath.
    - apply idpath.
    - exact (PathOver_pair
               (IHe₁ x)
               (IHe₂ x)).
    - apply idpath.
    - apply idpath.
    - apply idpath.
  Defined.
  
  Local Definition paths
        (j : path_label Σ)
        (x : poly_act (path_source Σ j) carrier)
    : sem_endpoint_UU (path_left Σ j) operation x
      =
      sem_endpoint_UU (path_right Σ j) operation x.
  Proof.
    use PathOverToTotalPath'.
    - refine (!(pr1_endpoint (path_left Σ j) x) @ _ @ pr1_endpoint (path_right Σ j) x).
      exact (alg_path X j (poly_pr1 (path_source Σ j) x)).
    - exact
        (composePathOver
           (inversePathOver (pr2_endpoint (path_left Σ j) x))
           (composePathOver
              (disp_alg_path
                 Y j
                 (poly_pr1 (path_source Σ j) x)
                 _)
              (pr2_endpoint (path_right Σ j) x))).
  Defined.
  
  Local Definition pr1_homot_endpoint
        {Q : poly_code}
        {TR : poly_code}
        {al ar : endpoint (point_constr Σ) Q TR}
        {T : poly_code}
        {sl sr : endpoint (point_constr Σ) Q T}
        (h : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
        (x : poly_act
               Q
               (∑ x, pr1 Y x))
        (p : sem_endpoint_UU al operation x
             =
             sem_endpoint_UU ar operation x)
    : maponpaths
        (poly_pr1 _)
        (sem_homot_endpoint_UU
           h
           (∑ z, pr1 Y z)
           operation paths
           x p)
      =
      !(pr1_endpoint _ _)
       @ sem_homot_endpoint_UU
           h
           (alg_carrier X)
           (alg_constr X)
           (alg_path X)
           (poly_pr1 _ x)
           (pr1_endpoint _ _
            @ maponpaths (poly_pr1 _) p
            @ !(pr1_endpoint _ _))
       @ pr1_endpoint _ _.
  Proof.
    induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | T₁ T₂ e₁ e₂ e₃ e₄ h IHh | T₁ T₂ e₁ e₂ e₃ e₄ h IHh
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                    | j e | el er | ].
    - (* identity *)
      exact (!pathsinv0l _).
    - (* symmetry *)
      simpl.
      refine (maponpathsinv0 _ _ @ _).
      refine (maponpaths (λ z, !z) IHh @ _).
      refine (pathscomp_inv _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp_inv.
      }
      refine (!(path_assoc _ _ _) @ _).
      do 2 apply maponpaths.
      apply pathsinv0inv0.
    - (* transitivity *)
      simpl.
      refine (maponpathscomp0 _ _ _ @ _).
      refine (maponpaths (λ z, z @ _) IHh₁ @ _).
      refine (maponpaths (λ z, _ @ z) IHh₂ @ _).
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
      apply maponpaths.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply pathsinv0r.
      }
      apply idpath.
    - (* associativity *)
      simpl.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply pathscomp_inv.
        }
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpathscomp0.
          }
          apply maponpaths_2.
          apply maponpathscomp.
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply pathsinv0l.
      }
      simpl.
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply pathscomp_inv.
        }
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        apply pathsinv0l.
      }
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp0rid.
      }
      apply pathsinv0l.
    - (* left identity *)
      exact (!pathsinv0l _).
    - (* right identity *)
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (pathscomp0rid _ @ _).
        apply maponpathsidfun.
      }
      apply pathsinv0l.
    - (* first projection *)
      simpl ; simpl in IHh.
      refine (_ @ maponpaths (maponpaths pr1) IHh @ _).
      + refine (_ @ !(maponpathscomp (dirprodf (poly_pr1 T₁) (poly_pr1 T₂)) pr1 _)).
        exact (maponpathscomp
                 pr1
                 (poly_pr1 T₁)
                 (sem_homot_endpoint_UU
                    h
                    (∑ z, pr1 Y z)
                    operation paths
                    x p)).
      + etrans.
        {
          etrans.
          {
            apply maponpathscomp0.
          }
          apply maponpaths.
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply maponpaths_pr1_pathsdirprod.
        }
        do 2 apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
    - (* second projection *)
      simpl ; simpl in IHh.
      refine (_ @ maponpaths (maponpaths dirprod_pr2) IHh @ _).
      + refine (_ @ !(maponpathscomp (dirprodf (poly_pr1 T₁) (poly_pr1 T₂)) pr2 _)).
        exact (maponpathscomp
                 dirprod_pr2
                 (poly_pr1 T₂)
                 (sem_homot_endpoint_UU
                    h
                    (∑ z, pr1 Y z)
                    operation paths
                    x p)).
      + etrans.
        {
          etrans.
          {
            apply maponpathscomp0.
          }
          apply maponpaths.
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply maponpaths_pr2_pathsdirprod.
        }
        do 2 apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
    - (* pair of endpoints *)
      simpl.
      etrans.
      {
        refine (!_).
        apply maponpaths_pathsdirprod.
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_concat.
        }
        etrans.
        {
          apply maponpaths_2.
          apply pathsdirprod_inv.
        }
        apply pathsdirprod_concat.
      }
      refine (!_).
      exact (paths_pathsdirprod IHh₁ IHh₂).
    - (* left inclusion *)
      simpl.
      refine (coprodf_path_maponpaths_inl _ _ _ @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathsinv0.
        }
        refine (!_).
        apply (maponpathscomp0 inl).
      }
      apply maponpaths.
      exact (!IHh).
    - (* right inclusion *)
      simpl.
      refine (coprodf_path_maponpaths_inr _ _ _ @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathsinv0.
        }
        refine (!_).
        apply (maponpathscomp0 inr).
      }
      apply maponpaths.
      exact (!IHh).
    - (* path constructor *)
      simpl.
      etrans.
      {
        exact (maponpaths_pr1_PathOverToTotalPath'
                 _
                 (composePathOver
                    (inversePathOver (pr2_endpoint (path_left Σ j) _))
                    (composePathOver
                       (disp_alg_path
                          Y j
                          (poly_pr1 (path_source Σ j) _)
                          _)
                       (pr2_endpoint (path_right Σ j) _)))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp_inv.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      refine (!_).
      refine (homotsec_natural
               (alg_path X j)
               (pr1_endpoint e x)
               @ _).
      apply maponpaths_2.
      apply maponpathsinv0.
    - (* point constructor *)
      simpl.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply pathscomp0rid.
          }
          refine (!_).
          apply maponpathsinv0.
        }
        etrans.
        {
          do 2 apply maponpaths.
          apply pathscomp0rid.
        }
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply maponpathscomp0.
        }
        refine (!_).
        apply maponpathscomp0.
      }
      refine (!_).
      etrans.
      {
        apply (maponpathscomp operation pr1).
      }
      etrans.
      {
        exact (!(maponpathscomp (poly_pr1 _) (alg_constr X) _)).
      }
      exact (maponpaths (maponpaths (alg_constr X)) IHh).
    - (* path argument *)
      simpl.
      refine (!_).
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          apply pathsinv0l.
        }
        simpl.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
  Qed.

  Local Definition PathOver_poly_pr2_operation
        {x₁ x₂ : poly_act (point_constr Σ) carrier}
        (q : x₁ = x₂)
    : globe_over
        Y
        (maponpathscomp operation pr1 _
         @ !(maponpathscomp (poly_pr1 _) (alg_constr X) _))
        (PathOver_poly_pr2 I (maponpaths operation q))
        (@apd_2
           _ _
           (poly_dact (point_constr Σ) (pr1 Y))
           (poly_dact I (pr1 Y))
           (alg_constr X)
           (disp_alg_constr Y)
           _ _ _ _ _
           (PathOver_poly_pr2 (point_constr Σ) q)).
  Proof.
    induction q.
    unfold globe_over.
    cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply PathOver_poly_pr2_is_idpath.
    }
    apply idpath.
  Qed.    

  Local Definition pr2_homot_endpoint
        {Q : poly_code}
        {TR : poly_code}
        {al ar : endpoint (point_constr Σ) Q TR}
        {T : poly_code}
        {sl sr : endpoint (point_constr Σ) Q T}
        (h : homot_endpoint (path_left Σ) (path_right Σ) al ar sl sr)
        (x : poly_act
               Q
               (∑ x, pr1 Y x))
        (p : sem_endpoint_UU al operation x
             =
             sem_endpoint_UU ar operation x)
    : globe_over
        (poly_dact T (pr1 Y))
        (pr1_homot_endpoint h x p)
        (PathOver_poly_pr2
           _
           (sem_homot_endpoint_UU
              h
              (∑ x0 : path_alg_carrier (pr1 X), pr1 Y x0)
              operation paths x p))
        (composePathOver
           (inversePathOver (pr2_endpoint _ _))
           (composePathOver
              (homot_endpoint_dact
                 h
                 (disp_alg_constr Y)
                 (disp_alg_path Y)
                 _
                 (composePathOver
                    (pr2_endpoint _ _)
                    (composePathOver
                       (PathOver_poly_pr2 _ p)
                       (inversePathOver (pr2_endpoint _ _)))))
              (pr2_endpoint _ _))).
  Proof.
    induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | T₁ T₂ e₁ e₂ e₃ e₄ h IHh | T₁ T₂ e₁ e₂ e₃ e₄ h IHh
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                    | j e | el er | ].
    - (* identity *)
      use globe_over_move_globe_one_type.
      { apply poly_act_hlevel. }
      { exact (!(pathsinv0l _)). }
      use inv_globe_over.
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      simple refine (concat_globe_over
                       (globe_over_compose_left'
                          (inversePathOver (pr2_endpoint e x))
                          (globe_over_id_left (pr2_endpoint e x)))
                       (concat_globe_over
                          (globe_over_inv_left _)
                          _)).
      { apply idpath. }
      exact (!(PathOver_poly_pr2_is_idpath _ _)).
    - (* symmetry *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      simple refine
      (concat_globe_over
         (PathOver_pr1_PathOver_poly_inv _)
         (concat_globe_over
            (globe_over_on_inv IHh)
            (concat_globe_over
               (globe_over_comp_inv _ _)
               (concat_globe_over
                  (globe_over_compose_left'
                     _
                     (globe_over_inv_inv _))
                  (concat_globe_over
                     (globe_over_compose_right
                        (pr2_endpoint e₁ x)
                        (globe_over_comp_inv _ _)
                     )
                     (globe_over_assocr _ _ _)))))).
    - (* transitivity *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      simple refine
      (concat_globe_over
         (PathOver_pr1_PathOver_poly_concat _ _)
         (concat_globe_over
            (globe_over_compose_right _ IHh₁)
            (concat_globe_over
               (globe_over_compose_left' _ IHh₂)
               (concat_globe_over
                  (globe_over_assocr _ _ _)
                  (globe_over_compose_left'
                     _
                     (concat_globe_over
                        (globe_over_assocl _ _ _)
                        (concat_globe_over
                           (globe_over_assocl _ _ _)
                           (globe_over_compose_right
                              _
                              (globe_over_compose_right
                                 _
                                 (concat_globe_over
                                    (globe_over_assocr _ _ _)
                                    (concat_globe_over
                                       (globe_over_compose_left'
                                          _
                                          (globe_over_inv_right _))
                                       (globe_over_id_right _)))))))))))).
    - (* associativity *)
      simpl.
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      simple refine
      (concat_globe_over
         (PathOver_poly_pr2_is_idpath_globe _ _)
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (concat_globe_over
                     (globe_over_id_left _)
                     (globe_over_compose_right
                        _
                        (concat_globe_over
                           (apd2_concat _ _ _)
                           (globe_over_compose_right
                              _
                              (apd2_comp _ _ _))))))
               (concat_globe_over
                  (globe_over_compose_left'
                     _
                     (globe_over_assocr _ _ _))
                  (globe_over_inv_left _))))).
    - (* left identity *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      simple refine
      (concat_globe_over
         (PathOver_poly_pr2_is_idpath_globe _ _)
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (globe_over_id_left _))
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (globe_over_on_inv
                        (globe_over_id_left _)))
                  (globe_over_inv_left _))))).
    - (* right identity *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      simple refine
      (concat_globe_over
         (PathOver_poly_pr2_is_idpath_globe _ _)
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (globe_over_id_left _))
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (globe_over_on_inv
                        (concat_globe_over
                           (globe_over_id_right _)
                           (apd2_idfun _))))
                  (globe_over_inv_left _))))).
    - (* first projection *)
      simple refine
      (globe_over_move_globe_one_type
         _
         (concat_globe_over
            (PathOver_pr1_PathOver_poly_pr2
               (sem_homot_endpoint_UU
                  h
                  (∑ x0, pr1 Y x0)
                  operation paths
                  x p))
            (concat_globe_over
               (globe_over_pr1 IHh)
               (concat_globe_over
                  (PathOver_pr1_concat _ _)
                  (concat_globe_over
                     (globe_over_compose_right
                        _
                        (concat_globe_over
                           (PathOver_pr1_inv _)
                           (globe_over_on_inv (PathOver_pr1_pair _ _))))
                     (globe_over_compose_left'
                        _
                        (concat_globe_over
                           (PathOver_pr1_concat _ _)
                           (globe_over_compose_left'
                              _
                              (PathOver_pr1_pair _ _)))))))))
      ; try apply poly_act_hlevel.
    - (* second projection *)
      simple refine
      (globe_over_move_globe_one_type
         _
         (concat_globe_over
            (PathOver_pr2_PathOver_poly_pr2
               (sem_homot_endpoint_UU
                  h
                  (∑ x0, pr1 Y x0)
                  operation paths
                  x p))
            (concat_globe_over
               (globe_over_pr2 IHh)
               (concat_globe_over
                  (PathOver_pr2_concat _ _)
                  (concat_globe_over
                     (globe_over_compose_right
                        _
                        (concat_globe_over
                           (PathOver_pr2_inv _)
                           (globe_over_on_inv (PathOver_pr2_pair _ _))))
                     (globe_over_compose_left'
                        _
                        (concat_globe_over
                           (PathOver_pr2_concat _ _)
                           (globe_over_compose_left'
                              _
                              (PathOver_pr2_pair _ _)))))))))
      ; try apply poly_act_hlevel.
    - (* pair of endpoints *)
      refine (globe_over_move_globe_one_type _ _).
      { apply (poly_act_hlevel (T₁ * T₂)). }
      simple refine
      (concat_globe_over
         (PathOver_pr2_PathOver_pair _ _)
         (concat_globe_over
            (globe_over_PathOver_pair IHh₁ IHh₂)
            (concat_globe_over
               (PathOver_pair_concat _ _ _ _)
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (PathOver_pair_inv _ _))
                  (globe_over_compose_left'
                     _
                     (PathOver_pair_concat _ _ _ _)))))).
    - (* left inclusion *)
      refine (globe_over_move_globe_one_type _ _).
      { apply (poly_act_hlevel (_ + _)). }
      simple refine
      (concat_globe_over
         (PathOver_pr1_PathOver_poly_inl
            (sem_homot_endpoint_UU
               h
               (∑ x0, pr1 Y x0)
               operation paths
               x p))
         (concat_globe_over
            (globe_over_inl IHh)
            (concat_globe_over
               (PathOver_inl_concat _ _)
               (concat_globe_over
                  (globe_over_compose_left'
                     _
                     (PathOver_inl_concat _ _))
                  (concat_globe_over
                     (globe_over_compose_right
                        _
                        (PathOver_inl_inv _))
                     (inv_globe_over
                        (concat_globe_over
                           (globe_over_compose_right
                              _
                              (globe_over_on_inv
                                 (concat_globe_over
                                    (globe_over_id_right _)
                                    (apd2_inl _))))
                           (globe_over_compose_left'
                              _
                              (globe_over_compose_left'
                                 _
                                 (concat_globe_over
                                    (globe_over_id_right _)
                                    (apd2_inl _))))))))))).
    - (* right inclusion *)
      refine (globe_over_move_globe_one_type _ _).
      { apply (poly_act_hlevel (_ + _)). }
      simple refine
      (concat_globe_over
         (PathOver_pr1_PathOver_poly_inr
            (sem_homot_endpoint_UU
               h
               (∑ x0, pr1 Y x0)
               operation paths
               x p))
         (concat_globe_over
            (globe_over_inr IHh)
            (concat_globe_over
               (PathOver_inr_concat _ _)
               (concat_globe_over
                  (globe_over_compose_left'
                     _
                     (PathOver_inr_concat _ _))
                  (concat_globe_over
                     (globe_over_compose_right
                        _
                        (PathOver_inr_inv _))
                     (inv_globe_over
                        (concat_globe_over
                           (globe_over_compose_right
                              _
                              (globe_over_on_inv
                                 (concat_globe_over
                                    (globe_over_id_right _)
                                    (apd2_inr _))))
                           (globe_over_compose_left'
                              _
                              (globe_over_compose_left'
                                 _
                                 (concat_globe_over
                                    (globe_over_id_right _)
                                    (apd2_inr _))))))))))).
    - (* path constructor *)
      simpl.
      refine (globe_over_move_globe_one_type _ _).
      { apply one_type_isofhlevel. }
      simple refine
      (concat_globe_over
         (TotalPathToPathOver_PathOverToTotalPath' _ _)
         (inv_globe_over
            (concat_globe_over
               (globe_over_compose_right
                  _
                  (globe_over_comp_inv _ _))
               (concat_globe_over
                  (globe_over_assocr _ _ _)
                  (globe_over_compose_left'
                     _
                     (concat_globe_over
                        (globe_over_assocl _ _ _)
                        (concat_globe_over
                           (globe_over_assocl _ _ _)
                           (globe_over_compose_right
                              _
                              (PathOver_natural
                                 _
                                 (disp_alg_path Y j)
                                 (pr2_endpoint e x)))))))))).
      apply one_type_isofhlevel.
    - (* point constructor *)
      refine (globe_over_move_globe_one_type _ _).
      { apply one_type_isofhlevel. }
      simple refine
      (concat_globe_over
         (PathOver_poly_pr2_operation _)
         (concat_globe_over
            (apd2_globe_over _ IHh)
            (concat_globe_over
               (apd2_concat _ _ _)
               (concat_globe_over
                  (globe_over_compose_left'
                     _
                     (apd2_concat _ _ _))
                  (inv_globe_over
                     (concat_globe_over
                        (globe_over_compose_left'
                           _
                           (globe_over_compose_left'
                              _
                              (globe_over_id_right _)))
                        (globe_over_compose_right
                           _
                           (concat_globe_over
                              (globe_over_on_inv
                                 (globe_over_id_right  _))
                              (apd2_inv _ _))))))))).      
    - (* path argument *)
      refine (globe_over_move_globe_one_type _ _).
      { apply poly_act_hlevel. }
      simple refine
      (inv_globe_over
         (concat_globe_over
            (globe_over_compose_left'
               _
               (concat_globe_over
                  (globe_over_assocr _ _ _)
                  (globe_over_compose_left'
                     _
                     (concat_globe_over
                        (globe_over_assocr _ _ _)
                        (concat_globe_over
                           (globe_over_compose_left'
                              _
                              (globe_over_inv_left _))
                           (globe_over_id_right _))))))
            (concat_globe_over
               (globe_over_assocl _ _ _)
               (concat_globe_over
                  (globe_over_compose_right
                     _
                     (globe_over_inv_left _))
                  (globe_over_id_left _))))).
  Qed.
  
  Local Definition homots
        (j : homot_label Σ)
        (x : poly_act
               (homot_point_arg Σ j)
               (∑ x, pr1 Y x))
        (p : sem_endpoint_UU (homot_path_arg_left Σ j) operation x
             =
             sem_endpoint_UU (homot_path_arg_right Σ j) operation x)
    : sem_homot_endpoint_one_types
        (homot_left_path Σ j)
        total_prealgebra paths
        x p
      =
      sem_homot_endpoint_one_types
        (homot_right_path Σ j)
        total_prealgebra paths
        x p.
  Proof.
    unfold sem_homot_endpoint_one_types.
    cbn.
    refine (path_is_PathOverToTotalPath' _ @ _).
    refine (_ @ !(path_is_PathOverToTotalPath' _)).
    use globe_over_to_homot.
    - refine (pr1_homot_endpoint (homot_left_path Σ j) _ _
              @ _
              @ !(pr1_homot_endpoint (homot_right_path Σ j) _ _)).
      refine (maponpaths (λ z, _ @ (z @ _)) _).
      exact (alg_homot
               X j
               (poly_pr1 _ x)
               ((pr1_endpoint _ x)
                @ maponpaths (poly_pr1 _) p
                @ !(pr1_endpoint _ x))).
    - simpl.
      simple refine
             (concat_globe_over
                (pr2_homot_endpoint
                   (homot_left_path Σ j)
                   x p)
                (concat_globe_over
                   _
                   (inv_globe_over
                      (pr2_homot_endpoint
                         (homot_right_path Σ j)
                         x p)))).
      use globe_over_compose_left.
      use globe_over_compose_right.
      apply (disp_alg_homot
               Y j
               (poly_pr1 _ x)
               (poly_pr2 _ x)
               ((pr1_endpoint _ x)
                @ maponpaths
                    (poly_pr1 (homot_path_arg_target Σ j))
                    p
                @ !(pr1_endpoint _ x))
               _).
  Qed.
    
  Definition total_algebra
    : hit_algebra_one_types Σ.
  Proof.
    use make_algebra.
    - use make_hit_path_algebra.
      + exact total_prealgebra.
      + exact paths.
    - exact homots.
  Defined.
End TotalAlgebra.

(**
We can project the total algebra on `X`.
 *)
Section Projection.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}.
  Variable (Y : disp_algebra X).

  Definition projection_help
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (carrier Y))
    : pr1_endpoint Y e _
      @ @sem_endpoint_UU_natural
          (point_constr Σ)
          P Q e
          (∑ x0 : path_alg_carrier (pr1 X), pr1 Y x0) _ (operation Y) 
          (pr211 X)
          pr1
          (λ _, idpath _)
          x
      =
      idpath _.
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | Z₁ Z₂ f | ]
    ; try (apply idpath).
    - simpl.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply IHe₂.
      }
      simpl.
      etrans.
      {
        refine (!_).
        apply maponpathscomp0.
      }
      etrans.
      {
        apply maponpaths.
        apply IHe₁.
      }
      apply idpath.
    - simpl.
      etrans.
      {
        apply pathsdirprod_concat.
      }
      exact (paths_pathsdirprod (IHe₁ x) (IHe₂ x)).
  Defined.

  Definition projection
    : total_algebra Y --> X.
  Proof.
    use make_algebra_map.
    - use make_hit_path_alg_map.
      + use tpair.
        * exact pr1.
        * use make_invertible_2cell.
          ** intro.
             apply idpath.
          ** apply one_type_2cell_iso.
      + intros i x.
        simpl.
        etrans.
        {
          apply maponpaths_2.
          unfold paths.
          exact (maponpaths_pr1_PathOverToTotalPath
                   _
                   (composePathOver
                      (inversePathOver (pr2_endpoint Y (path_left Σ i) x))
                      (composePathOver
                         (disp_alg_path
                            Y i (poly_pr1 (path_source Σ i) x)
                            (poly_pr2 (path_source Σ i) x))
                         (pr2_endpoint Y (path_right Σ i) x)))).
        }
        etrans.
        {
          refine (!(path_assoc _ _ _) @ _).
          apply maponpaths.
          refine (!(path_assoc _ _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply (projection_help (path_right Σ i)).
          }
          apply pathscomp0rid.
        }
        apply maponpaths_2.
        apply pathsinv0_to_right'.
        refine (!_).
        apply (projection_help (path_left Σ i)).
  Defined.
End Projection.
