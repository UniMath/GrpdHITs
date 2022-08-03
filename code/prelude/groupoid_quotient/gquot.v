(** The groupoid quotient *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import prelude.cubical_methods.

Local Open Scope cat.

(** * The groupoid quotient over a type. *)
(** Given a type [A] and a groupoid [G], we construct a type [gquot G] such that
    we have [A -> gquot A G] and the equality of [gquot A G] is described by [G].
    We use the standard method to define the HIT
    <<
    HIT gquot G :=
     | gcl : A -> gquot G
     | gcleq : Π(a₁ a₂ : A), hom G a₁ a₂ -> gcl a₁ = gcl a₂
     | ge : Π(a : A), gcleq (e a) = idpath
     | ginv : Π(a₁ a₂ : A) (g : hom G a₁ a₂), gcleq g⁻¹ = (gcleq g)^
     | gconcat : Π(a₁ a₂ a₃ : A) (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
               gcleq (g₁ × g₂) = gcleq g₁ @ gcleq g₂
     | gtrunc : Is-1-Type (gquot G)
    >>
*)
Module Export gquot.
  Private Inductive gquot (G : groupoid) : UU :=
  | gcl : ob G → gquot G.

  Axiom gcleq
    : ∏ (G : groupoid) {a₁ a₂ : G} (g : a₁ --> a₂),
      gcl G a₁ = gcl G a₂.

  Axiom ge
    : ∏ (G : groupoid) (a : G),
      gcleq G (identity a) = idpath _.

  Axiom gconcat
    : ∏ (G : groupoid)
        {a₁ a₂ a₃ : G}
        (g₁ : a₁ --> a₂) (g₂ : a₂ --> a₃),
      gcleq G (g₁ · g₂) = gcleq G g₁ @ gcleq G g₂.

  Definition ginv
    : ∏ (G : groupoid) {a₁ a₂ : G} (g : a₁ --> a₂),
      gcleq G (inv_from_z_iso (g ,, pr2 G _ _ g)) = !(gcleq G g).
  Proof.
    intros G a₁ a₂ g.
    apply path_inverse_from_right.
    rewrite pathsinv0inv0.
    rewrite <- gconcat.
    etrans.
    {
      apply maponpaths.
      exact (z_iso_inv_after_z_iso (g ,, pr2 G a₁ a₂ g)).
    }
    exact (ge _ a₁).
  Qed.
  
  Axiom gtrunc
    : ∏ (G : groupoid), isofhlevel 3 (gquot G).

  Section gquot_ind.
    Variable (G : groupoid)
             (Y : gquot G → UU)
             (gclY : ∏ (a : G), Y(gcl G a))
             (gcleqY : ∏ (a₁ a₂ : G) (g : a₁ --> a₂),
                 PathOver (gcleq G g) (gclY a₁) (gclY a₂))
             (geY : ∏ (a : G), globe_over
                                      Y
                                      (ge G a)
                                      (gcleqY a a (identity a))
                                      (idpath (gclY a)))
             (gconcatY : ∏ (a₁ a₂ a₃ : G)
                                (g₁ : a₁ --> a₂) (g₂ : a₂ --> a₃),
                 globe_over
                   Y
                   (gconcat G g₁ g₂)
                   (gcleqY a₁ a₃ (g₁ · g₂))
                   (composePathOver
                      (gcleqY a₁ a₂ g₁)
                      (gcleqY a₂ a₃ g₂)))
             (truncY : ∏ (x : gquot G), isofhlevel 3 (Y x)).

    Fixpoint gquot_ind (g : gquot G) : Y g
      := (match g with
         | gcl _ a => fun _ _ _ _ => gclY a
          end) gcleqY geY gconcatY truncY.

    Axiom gquot_ind_beta_gcleq : ∏ (a₁ a₂ : G) (g : a₁ --> a₂),
        apd gquot_ind (gcleq G g)
        =
        gcleqY a₁ a₂ g.
  End gquot_ind.
End gquot.

Arguments gquot_ind {G} Y gclY gcleqY geY gconcatY truncY.
