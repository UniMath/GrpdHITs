(** Here we define the signature for the integers modulo 2 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.

Local Open Scope cat.

(** MISSING HOMOTOPY ENDPOINTS *)
Definition TODO {A : UU} : A.
Admitted.

Definition comp_pair
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {P₁ P₂ P₃ : poly_code}
           (e₁ : endpoint A Q P₁)
           (e₂ : endpoint A P₁ P₂)
           (e₃ : endpoint A P₁ P₃)
  : homot_endpoint
      l r
      al ar
      (comp e₁ (pair e₂ e₃))
      (pair (comp e₁ e₂) (comp e₁ e₃)).
Proof.
  Print homot_endpoint.
  refine (trans_e
            _
            (path_pair _ _)).
  Print homot_endpoint.
  apply TODO.
Defined.

Definition monoidal_point_constr
  : poly_code
  := C unit_one_type + I * I.

Inductive monoidal_paths : UU :=
| lunit : monoidal_paths
| runit : monoidal_paths
| massoc : monoidal_paths.

Inductive monoidal_homots : UU :=
| triangle : monoidal_homots
| pentagon : monoidal_homots.

Definition monoidal_paths_args
  : monoidal_paths → poly_code.
Proof.
  intro i.
  induction i.
  - (* lunit *)
    exact I.
  - (* runit *)
    exact I.
  - (* massoc *)
    exact (I * I * I).
Defined.

Definition unit_endpoint
           (P : poly_code)
  : endpoint monoidal_point_constr P I
  := comp
       (comp
          (c P (tt : unit_one_type))
          (ι₁ _ _))
       constr.

Definition mult_endpoint
           {P : poly_code}
           (e₁ e₂ : endpoint monoidal_point_constr P I)
  : endpoint monoidal_point_constr P I
  := comp
       (comp
          (pair e₁ e₂)
          (ι₂ _ _))
       constr.

Definition monoidal_paths_lhs
           (i : monoidal_paths)
  : endpoint monoidal_point_constr (monoidal_paths_args i) I.
Proof.
  induction i.
  - (* lunit *)
    exact (mult_endpoint
             (unit_endpoint _)
             (id_e _ _)).
  - (* runit *)
    exact (mult_endpoint
             (id_e _ _)
             (unit_endpoint _)).
  - (* massoc *)
    exact (mult_endpoint
             (comp (π₁ _ _) (π₁ _ _))
             (mult_endpoint
                (comp (π₁ _ _) (π₂ _ _))
                (π₂ _ _))).
Defined.

Definition monoidal_paths_rhs
           (i : monoidal_paths)
  : endpoint monoidal_point_constr (monoidal_paths_args i) I.
Proof.
  induction i.
  - (* lunit *)
    exact (id_e _ _).
  - (* runit *)
    exact (id_e _ _).
  - (* massoc *)
    exact (mult_endpoint
             (mult_endpoint
                (comp (π₁ _ _) (π₁ _ _))
                (comp (π₁ _ _) (π₂ _ _)))
             (π₂ _ _)).
Defined.

Definition monoidal_homots_point_arg
           (i : monoidal_homots)
  : poly_code.
Proof.
  induction i.
  - (* triangle *)
    exact (I * I).
  - (* pentagon *)
    exact (I * I * I * I).
Defined.

Definition monoidal_homots_point_left_endpoint
           (i : monoidal_homots)
  : endpoint monoidal_point_constr (monoidal_homots_point_arg i) I.
Proof.
  induction i.
  - (* triangle *)
    exact (mult_endpoint
             (π₁ _ _)
             (mult_endpoint
                (unit_endpoint _)
                (π₂ _ _))).
  - (* pentagon *)
    exact (mult_endpoint
             (comp (π₁ _ _) (comp (π₁ _ _) (π₁ _ _)))
             (mult_endpoint
                (comp (π₁ _ _) (comp (π₁ _ _) (π₂ _ _)))
                (mult_endpoint
                   (comp (π₁ _ _) (π₂ _ _))
                   (π₂ _ _)))).
Defined.

Definition monoidal_homots_point_right_endpoint
           (i : monoidal_homots)
  : endpoint monoidal_point_constr (monoidal_homots_point_arg i) I.
Proof.
  induction i.
  - (* triangle *)
    exact (mult_endpoint
             (π₁ _ _)
             (π₂ _ _)).
  - (* pentagon *)
    exact (mult_endpoint
             (mult_endpoint
                (mult_endpoint
                   (comp (π₁ _ _) (comp (π₁ _ _) (π₁ _ _)))
                   (comp (π₁ _ _) (comp (π₁ _ _) (π₂ _ _))))
                (comp (π₁ _ _) (π₂ _ _)))
             (π₂ _ _)).
Defined.

Definition lunit_homot_endpoint
           {P : poly_code}
           (e : endpoint monoidal_point_constr P I)
  : homot_endpoint
      monoidal_paths_lhs
      monoidal_paths_rhs
      (c P (tt : unit_one_type))
      (c P (tt : unit_one_type))
      (mult_endpoint (unit_endpoint P) e)
      e.
Proof.
  refine (trans_e
            _
            (comp_id_r _)).
  refine (trans_e
            _
            (path_constr
               lunit
               _)).
  simpl.
  unfold mult_endpoint.
  refine (trans_e
            _
            (inv_e
               (comp_assoc _ _ _))).
  apply ap_e.
  refine (trans_e
            _
            (inv_e
               (comp_assoc _ _ _))).
  apply ap_e.
  unfold unit_endpoint.
  refine (trans_e
            (path_pair _ _)
            (inv_e (comp_pair _ _ _))).
  - refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply path_inl.
    apply inv_e.
    apply comp_constant.
  - apply inv_e.
    apply comp_id_r.
Defined.

Definition runit_homot_endpoint
           {P : poly_code}
           (e : endpoint monoidal_point_constr P I)
  : homot_endpoint
      monoidal_paths_lhs
      monoidal_paths_rhs
      (c P (tt : unit_one_type))
      (c P (tt : unit_one_type))
      (mult_endpoint e (unit_endpoint _))
      e.
Proof.
  refine (trans_e
            _
            (comp_id_r _)).
  refine (trans_e
            _
            (path_constr
               runit
               _)).
  simpl.
  unfold mult_endpoint.
  refine (trans_e
            _
            (inv_e
               (comp_assoc _ _ _))).
  apply ap_e.
  refine (trans_e
            _
            (inv_e
               (comp_assoc _ _ _))).
  apply ap_e.
  unfold unit_endpoint.
  refine (trans_e
            (path_pair _ _)
            (inv_e (comp_pair _ _ _))).
  - apply inv_e.
    apply comp_id_r.
  - refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply path_inl.
    apply inv_e.
    apply comp_constant.
Defined.

Definition assoc_homot_endpoint
           {P : poly_code}
           (e₁ e₂ e₃ : endpoint monoidal_point_constr P I)
  : homot_endpoint
      monoidal_paths_lhs
      monoidal_paths_rhs
      (c P (tt : unit_one_type))
      (c P (tt : unit_one_type))
      (mult_endpoint
         e₁
         (mult_endpoint
            e₂
            e₃))
      (mult_endpoint
         (mult_endpoint
            e₁
            e₂)
         e₃).
Proof.
  unfold mult_endpoint.
  refine (trans_e
            _
            (trans_e
               (path_constr massoc (pair (pair e₁ e₂) e₃))
               _))
  ; simpl ; unfold mult_endpoint.
  - refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (trans_e
              (path_pair _ _)
              (inv_e (comp_pair _ _ _))).
    + apply inv_e.
      refine (trans_e
                (comp_assoc _ _ _)
                _).
      refine (trans_e
                (ap_e _ (pair_π₁ _ _))
                _).
      apply pair_π₁.
    + refine (trans_e
                _
                (inv_e (comp_assoc _ _ _))).
      apply ap_e.
      refine (trans_e
                _
                (inv_e (comp_assoc _ _ _))).
      apply ap_e.
      refine (trans_e
                (path_pair _ _)
                (inv_e (comp_pair _ _ _))).
      * apply inv_e.
        refine (trans_e
                  (comp_assoc _ _ _)
                  _).
        refine (trans_e
                  (ap_e _ (pair_π₁ _ _))
                  _).
        apply pair_π₂.
      * apply inv_e.
        apply pair_π₂.
  - refine (trans_e
              (comp_assoc _ _ _)
              _).
    apply ap_e.
    refine (trans_e
              (comp_assoc _ _ _)
              _).
    apply ap_e.
    refine (trans_e
              (comp_pair _ _ _)
              (path_pair _ _)).
    + refine (trans_e
                (comp_assoc _ _ _)
                _).
      apply ap_e.
      refine (trans_e
                (comp_assoc _ _ _)
                _).
      apply ap_e.
      refine (trans_e
                (comp_pair _ _ _)
                (path_pair _ _)).
      * refine (trans_e
                  (comp_assoc _ _ _)
                  _).
        refine (trans_e
                  (ap_e _ (pair_π₁ _ _))
                  _).
        apply pair_π₁.
      * refine (trans_e
                  (comp_assoc _ _ _)
                  _).
        refine (trans_e
                  (ap_e _ (pair_π₁ _ _))
                  _).
        apply pair_π₂.
    + apply pair_π₂.
Defined.

Definition lwhisker_endpoint
           {P : poly_code}
           (e₁ : endpoint monoidal_point_constr P I)
           {e₂ e₃ : endpoint monoidal_point_constr P I}
           (h : homot_endpoint
                  monoidal_paths_lhs
                  monoidal_paths_rhs
                  (c P (tt : unit_one_type))
                  (c P (tt : unit_one_type))
                  e₂
                  e₃)
  : homot_endpoint
      monoidal_paths_lhs
      monoidal_paths_rhs
      (c P (tt : unit_one_type))
      (c P (tt : unit_one_type))
      (mult_endpoint e₁ e₂)
      (mult_endpoint e₁ e₃).
Proof.
  unfold mult_endpoint.
  use ap_e.
  use ap_e.
  use path_pair.
  - apply refl_e.
  - exact h.
Defined.

Definition rwhisker_endpoint
           {P : poly_code}
           {e₁ e₂ : endpoint monoidal_point_constr P I}
           (e₃ : endpoint monoidal_point_constr P I)
           (h : homot_endpoint
                  monoidal_paths_lhs
                  monoidal_paths_rhs
                  (c P (tt : unit_one_type))
                  (c P (tt : unit_one_type))
                  e₁
                  e₂)
  : homot_endpoint
      monoidal_paths_lhs
      monoidal_paths_rhs
      (c P (tt : unit_one_type))
      (c P (tt : unit_one_type))
      (mult_endpoint e₁ e₃)
      (mult_endpoint e₂ e₃).
Proof.
  unfold mult_endpoint.
  use ap_e.
  use ap_e.
  use path_pair.
  - exact h.
  - apply refl_e.
Defined.

Definition monoidal_homots_point_lhs
           (i : monoidal_homots)
  : homot_endpoint
      monoidal_paths_lhs
      monoidal_paths_rhs
      (c (monoidal_homots_point_arg i) (tt : unit_one_type))
      (c (monoidal_homots_point_arg i) (tt : unit_one_type))
      (monoidal_homots_point_left_endpoint i)
      (monoidal_homots_point_right_endpoint i).
Proof.
  induction i.
  - (* triangle *)
    exact (lwhisker_endpoint
             (π₁ I I)
             (lunit_homot_endpoint _)).
  - (* pentagon *)
    exact (trans_e
             (assoc_homot_endpoint _ _ _)
             (assoc_homot_endpoint _ _ _)).
Defined.

Definition monoidal_homots_point_rhs
           (i : monoidal_homots)
  : homot_endpoint
      monoidal_paths_lhs
      monoidal_paths_rhs
      (c (monoidal_homots_point_arg i) (tt : unit_one_type))
      (c (monoidal_homots_point_arg i) (tt : unit_one_type))
      (monoidal_homots_point_left_endpoint i)
      (monoidal_homots_point_right_endpoint i).
Proof.
  induction i.
  - (* triangle *)
    exact (trans_e
             (assoc_homot_endpoint _ _ _)
             (rwhisker_endpoint
                (π₂ I I)
                (runit_homot_endpoint _))).
  - (* pentagon *)
    exact (trans_e
             (lwhisker_endpoint
                _
                (assoc_homot_endpoint _ _ _))
             (trans_e
                (assoc_homot_endpoint _ _ _)
                (rwhisker_endpoint
                   _
                   (assoc_homot_endpoint _ _ _)))).
Defined.

Definition monoidal_signature
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact monoidal_point_constr.
  - exact monoidal_paths.
  - exact monoidal_paths_args.
  - exact monoidal_paths_lhs.
  - exact monoidal_paths_rhs.
  - exact monoidal_homots.
  - exact monoidal_homots_point_arg.
  - exact (λ _, C unit_one_type).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact monoidal_homots_point_left_endpoint.
  - exact monoidal_homots_point_right_endpoint.
  - exact monoidal_homots_point_lhs.
  - exact monoidal_homots_point_rhs.
Defined.

Section Monoidal2AlgebraProjections.
  Variable (X : hit_algebra_one_types monoidal_signature).
  (*
  Definition mod2_carrier
    : one_type
    := pr111 X.

  Definition mod2_Z
    : mod2_carrier
    := pr211 X (inl tt).

  Definition mod2_S
    : mod2_carrier → mod2_carrier
    := λ x, pr211 X (inr x).

  Definition mod2_mod
    : ∏ (x : mod2_carrier), mod2_S (mod2_S x) = x
    := pr21 X mod.

  Definition mod2_ap_mod
    : ∏ (n : mod2_carrier),
      maponpaths mod2_S (mod2_mod n)
      =
      mod2_mod (mod2_S n)
    := λ n,
       !(maponpathscomp inr (pr211 X) (mod2_mod n))
       @ maponpaths
           (maponpaths (pr211 X))
           (!(pathscomp0rid _))
       @ pr2 X ap_mod n (idpath _)
       @ pathscomp0rid _.
   *)
End Monoidal2AlgebraProjections.
