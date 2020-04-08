(** Here we define the signature for the circle *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.
Require Import initial_grpd_alg.W_poly.
Require Import initial_grpd_alg.initial_groupoid_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

Section HomotopyCoeq.
  Context (A B : one_type)
          (f g : A → B).
  
  Definition coeq_point_constr
    : poly_code
    := C B.

  Definition coeq_signature
    : hit_signature.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
    - exact coeq_point_constr.
    - exact unit.
    - exact (λ _, C A).
    - exact (λ _, comp (fmap f) constr).
    - exact (λ _, comp (fmap g) constr).
    - exact empty.
    - exact fromempty.
    - exact fromempty.
    - intro x ; induction x.
    - intro x ; induction x.
    - intro x ; induction x.
    - intro x ; induction x.
    - intro x ; induction x.
    - intro x ; induction x.
  Defined.

  (** Projections of coeq algebra *)
  Section CoeqProjections.
    Variable (X : hit_algebra_one_types coeq_signature).

    Definition coeq_base
      : B → alg_carrier X
      := alg_constr X.

    Definition coeq_loop
               (a : A)
      : coeq_base (f a) = coeq_base (g a)
      := alg_path X tt a.
  End CoeqProjections.

  (** Builder for coequalizer algebra *)
  Section CoeqAlgebraBuilder.

  End CoeqAlgebraBuilder.

  (** Projections for the 1-cells *)
  Section CoeqMapProjections.

  End CoeqMapProjections.

  (** Builder for the 1-cells *)
  Section CoeqMapBuilder.

  End CoeqMapBuilder.
  
  (** Projections for the 2-cells *)
  Section CoeqCellProjections.
  End CoeqCellProjections.

  (** Builder for the 2-cells *)
  Section CoeqCellBuilder.

  End CoeqCellBuilder.
  
  (** Coeq induction *)
  Section CoeqInduction.
    Context {X : hit_algebra_one_types coeq_signature}
            (Y : alg_carrier X → one_type)
            (Ybase : ∏ (b : B), Y (coeq_base X b))
            (Yloop : ∏ (a : A),
                     @PathOver
                       _ _ _
                       Y
                       (Ybase (f a)) (Ybase (g a))
                       (coeq_loop X a)).
    
    Definition make_coeq_disp_algebra
      : disp_algebra X.
    Proof.
      use make_disp_algebra.
      - exact Y.
      - intros x xx.
        exact (Ybase x).
      - intros j x y.
        induction j.
        exact (Yloop x).
      - intro j.
        induction j.
    Defined.

    Variable (HX : is_HIT coeq_signature X).

    (** Induction principle *)
    Definition coeq_ind_disp_algebra_map
      : disp_algebra_map make_coeq_disp_algebra
      := HX make_coeq_disp_algebra.

    Definition coeq_ind
      : ∏ (x : alg_carrier X), Y x
      := pr1 coeq_ind_disp_algebra_map.

    Definition coeq_ind_base
               (b : B)
      : coeq_ind (coeq_base X b) = Ybase b
      := pr12 coeq_ind_disp_algebra_map b.

    Definition coeq_ind_loop
               (a : A)
      : PathOver_square
          _
          (idpath _)
          (apd (pr1 coeq_ind_disp_algebra_map) (coeq_loop X a))
          (Yloop a)
          (coeq_ind_base (f a))
          (coeq_ind_base (g a)).
    Proof.
      pose (pr22 coeq_ind_disp_algebra_map tt a)
        as p.
      cbn in p.
      rewrite !pathscomp0rid in p.
      exact p.
    Qed.
  End CoeqInduction.

  (** Some notations *)
  Local Notation "'φ'" := (f : one_types ⟦ A , B ⟧).
  Local Notation "'χ'" := (g : one_types ⟦ A , B ⟧).

  (** The coequalizer *)
  Definition coeq_one_types_algebra
    := pr1 (hit_existence coeq_signature).

  Definition coeq_one_types_is_initial
    : is_initial _ coeq_one_types_algebra.
  Proof.
    apply HIT_is_initial.
    exact (pr2 (hit_existence coeq_signature)).
  Defined.
  
  Definition coeq_one_types
    : one_types
    := pr111 coeq_one_types_algebra.

  Definition coeq_one_types_base
    : one_types ⟦ B , coeq_one_types ⟧
    := coeq_base coeq_one_types_algebra.

  Definition coeq_one_types_loop
    : φ · coeq_one_types_base ==> χ · coeq_one_types_base
    := coeq_loop coeq_one_types_algebra.

  Definition TODO {Z : UU} : Z.
  Admitted.

  (** Mapping principles for coequalizer *)  
  Section CoeqUMPMap.
    Variable (C : one_types)
             (h : one_types ⟦ B , C ⟧)
             (hcom : φ · h ==> χ · h).

    Definition coeq_ump1
      : coeq_one_types --> C.
    Proof.
      apply TODO.
    Defined.

    Definition coeq_ump1_base
      : coeq_one_types_base · coeq_ump1 ==> h.
    Proof.
      apply TODO.
    Defined.

    Definition coeq_ump1_loop
      : coeq_one_types_loop ▹ coeq_ump1 • (_ ◃ coeq_ump1_base)
        =
        lassociator _ _ _ • (φ ◃ coeq_ump1_base) • hcom.
    Proof.
      apply TODO.
    Qed.
  End CoeqUMPMap.

  Section CoeqUMPCell.
    Variable (C : one_types)
             (h : one_types ⟦ B , C ⟧)
             (hcom : φ · h ==> χ · h)
             (m₁ m₂ : coeq_one_types --> C)
             (m₁base : coeq_one_types_base · m₁ ==> h)
             (m₂base : coeq_one_types_base · m₂ ==> h)
             (m₁loop : coeq_one_types_loop ▹ m₁ • (_ ◃ m₁base)
                       =
                       lassociator _ _ _ • (φ ◃ m₁base) • hcom)
             (m₂loop : coeq_one_types_loop ▹ m₂ • (_ ◃ m₂base)
                       =
                       lassociator _ _ _ • (φ ◃ m₂base) • hcom).

    Definition coeq_ump2
      : m₁ ==> m₂.
    Proof.
      apply TODO.
    Defined.

    Definition coeq_ump2_base
      : (coeq_one_types_base ◃ coeq_ump2) • m₂base = m₁base.
    Proof.
      apply TODO.
    Qed.
  End CoeqUMPCell.

  Section CoeqUMPEq.
    Variable (C : one_types)
             (h : one_types ⟦ B , C ⟧)
             (hcom : φ · h ==> χ · h)
             (m₁ m₂ : coeq_one_types --> C)
             (m₁base : coeq_one_types_base · m₁ ==> h)
             (m₂base : coeq_one_types_base · m₂ ==> h)
             (m₁loop : coeq_one_types_loop ▹ m₁ • (_ ◃ m₁base)
                       =
                       lassociator _ _ _ • (φ ◃ m₁base) • hcom)
             (m₂loop : coeq_one_types_loop ▹ m₂ • (_ ◃ m₂base)
                       =
                       lassociator _ _ _ • (φ ◃ m₂base) • hcom)
             (τ₁ τ₂ : m₁ ==> m₂)
             (τ₁base : (coeq_one_types_base ◃ τ₁) • m₂base = m₁base)
             (τ₂base : (coeq_one_types_base ◃ τ₂) • m₂base = m₁base).

    Definition coeq_ump_eq
      : τ₁ = τ₂.
    Proof.
      apply TODO.
    Qed.
  End CoeqUMPEq.
End HomotopyCoeq.
