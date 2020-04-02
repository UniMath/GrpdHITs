(**
Here we define the signature for the coherent 2-groups.
A coherent 2-group has a unit, a multiplication, and an inverse operation.
The inverse laws are witnessed up to adjoint equivalence while associativity and unitality are witnessed as in a monoidal category.

For more details, see:
- https://ncatlab.org/nlab/show/2-group#definition
- Definition 7 in https://arxiv.org/pdf/math/0307200.pdf
 *)
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

Definition coh_2gr_point_constr
  : poly_code
  := C unit_one_type + I + I * I.

Inductive coh_2gr_paths : UU :=
| lunit : coh_2gr_paths
| runit : coh_2gr_paths
| linv : coh_2gr_paths
| rinv : coh_2gr_paths
| massoc : coh_2gr_paths.

Inductive coh_2gr_homots : UU :=
| inv_adj_triangle_l : coh_2gr_homots
| inv_adj_triangle_r : coh_2gr_homots
| triangle : coh_2gr_homots
| pentagon : coh_2gr_homots.

Definition coh_2gr_paths_args
  : coh_2gr_paths → poly_code.
Proof.
  intro i.
  induction i.
  - (* lunit *)
    exact I.
  - (* runit *)
    exact I.
  - (* linv *)
    exact I.
  - (* rinv *)
    exact I.
  - (* massoc *)
    exact (I * I * I).
Defined.

Definition unit_endpoint
           (P : poly_code)
  : endpoint coh_2gr_point_constr P I
  := comp
       (comp
          (comp
             (c P (tt : unit_one_type))
             (ι₁ _ _))
          (ι₁ _ _))
       constr.

Definition inv_endpoint
           {P : poly_code}
           (e : endpoint coh_2gr_point_constr P I)
  : endpoint coh_2gr_point_constr P I
  := comp
       (comp
          (comp
             e
             (ι₂ _ _))
          (ι₁ _ _))
       constr.

Definition mult_endpoint
           {P : poly_code}
           (e₁ e₂ : endpoint coh_2gr_point_constr P I)
  : endpoint coh_2gr_point_constr P I
  := comp
       (comp
          (pair e₁ e₂)
          (ι₂ _ _))
       constr.

Definition coh_2gr_paths_lhs
           (i : coh_2gr_paths)
  : endpoint coh_2gr_point_constr (coh_2gr_paths_args i) I.
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
  - (* linv *)
    exact (mult_endpoint
             (inv_endpoint (id_e _ _))
             (id_e _ _)).
  - (* rinv *)
    exact (unit_endpoint _).
  - (* massoc *)
    exact (mult_endpoint
             (comp (π₁ _ _) (π₁ _ _))
             (mult_endpoint
                (comp (π₁ _ _) (π₂ _ _))
                (π₂ _ _))).
Defined.

Definition coh_2gr_paths_rhs
           (i : coh_2gr_paths)
  : endpoint coh_2gr_point_constr (coh_2gr_paths_args i) I.
Proof.
  induction i.
  - (* lunit *)
    exact (id_e _ _).
  - (* runit *)
    exact (id_e _ _).
  - (* linv *)
    exact (unit_endpoint _).
  - (* rinv *)
    exact (mult_endpoint
             (id_e _ _)
             (inv_endpoint (id_e _ _))).
  - (* massoc *)
    exact (mult_endpoint
             (mult_endpoint
                (comp (π₁ _ _) (π₁ _ _))
                (comp (π₁ _ _) (π₂ _ _)))
             (π₂ _ _)).
Defined.

Definition coh_2gr_homots_point_arg
           (i : coh_2gr_homots)
  : poly_code.
Proof.
  induction i.
  - (* inv_adj_triangle_l *)
    exact I.
  - (* inv_adj_triangle_r *)
    exact I.
  - (* triangle *)
    exact (I * I).
  - (* pentagon *)
    exact (I * I * I * I).
Defined.

Definition coh_2gr_homots_point_left_endpoint
           (i : coh_2gr_homots)
  : endpoint coh_2gr_point_constr (coh_2gr_homots_point_arg i) I.
Proof.
  induction i.
  - (* inv_adj_triangle_l *)
    exact (mult_endpoint
             (unit_endpoint _)
             (id_e _ _)).
  - (* inv_adj_triangle_r *)
    exact(mult_endpoint
            (inv_endpoint (id_e _ _))
            (unit_endpoint _)).
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

Definition coh_2gr_homots_point_right_endpoint
           (i : coh_2gr_homots)
  : endpoint coh_2gr_point_constr (coh_2gr_homots_point_arg i) I.
Proof.
  induction i.
  - (* inv_adj_triangle_l *)
    exact (mult_endpoint
             (id_e _ _)
             (unit_endpoint _)).
  - (* inv_adj_triangle_r *)
    exact(mult_endpoint
            (unit_endpoint _)
            (inv_endpoint (id_e _ _))).
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
           (e : endpoint coh_2gr_point_constr P I)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
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
    refine (trans_e
              (comp_assoc _ _ _)
              _).
    apply ap_e.
    apply comp_constant.
  - apply inv_e.
    apply comp_id_r.
Defined.

Definition runit_homot_endpoint
           {P : poly_code}
           (e : endpoint coh_2gr_point_constr P I)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
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
    refine (trans_e (comp_assoc _ _ _) _).
    apply ap_e.
    apply comp_constant.
Defined.

Definition linv_homot_endpoint
           {P : poly_code}
           (e : endpoint coh_2gr_point_constr P I)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
      (c P (tt : unit_one_type))
      (c P (tt : unit_one_type))
      (mult_endpoint (inv_endpoint e) e)
      (unit_endpoint P).
Proof.
  refine (trans_e
            (trans_e
               _
               (path_constr linv e))
            _)
  ; cbn.
  - unfold mult_endpoint.
    refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (trans_e
              _
              (inv_e (comp_pair _ _ _))).
    use path_pair.
    + unfold inv_endpoint.
      refine (trans_e
                _
                (inv_e (comp_assoc _ _ _))).
      apply ap_e.
      refine (trans_e
                _
                (inv_e (comp_assoc _ _ _))).
      apply ap_e.
      refine (trans_e
                _
                (inv_e (comp_assoc _ _ _))).
      apply ap_e.
      refine (inv_e _).
      apply comp_id_r.
    + refine (inv_e _).
      apply comp_id_r.
  - unfold unit_endpoint.
    refine (trans_e
              (comp_assoc _ _ _)
              _).
    apply ap_e.
    refine (trans_e
              (comp_assoc _ _ _)
              _).
    apply ap_e.
    refine (trans_e
              (comp_assoc _ _ _)
              _).
    apply ap_e.
    apply comp_constant.
Defined.
    
Definition rinv_homot_endpoint
           {P : poly_code}
           (e : endpoint coh_2gr_point_constr P I)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
      (c P (tt : unit_one_type))
      (c P (tt : unit_one_type))
      (unit_endpoint P)
      (mult_endpoint e (inv_endpoint e)).
Proof.
  refine (trans_e
            (trans_e
               _
               (path_constr rinv e))
            _)
  ; cbn.
  - unfold unit_endpoint.
    cbn.
    refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (trans_e
              _
              (inv_e (comp_assoc _ _ _))).
    apply ap_e.
    refine (inv_e _).
    apply comp_constant.
  - unfold mult_endpoint.
    refine (trans_e
              (comp_assoc _ _ _)
              _).
    apply ap_e.
    refine (trans_e
              (comp_assoc _ _ _)
              _).
    apply ap_e.
    refine (trans_e
              (comp_pair _ _ _)
              _).
    use path_pair.
    + apply comp_id_r.
    + unfold inv_endpoint.
      refine (trans_e
                (comp_assoc _ _ _)
                _).
      apply ap_e.
      refine (trans_e
                (comp_assoc _ _ _)
                _).
      apply ap_e.
      refine (trans_e
                (comp_assoc _ _ _)
                _).
      apply ap_e.
      apply comp_id_r.
Defined.

Definition assoc_homot_endpoint
           {P : poly_code}
           (e₁ e₂ e₃ : endpoint coh_2gr_point_constr P I)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
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
           (e₁ : endpoint coh_2gr_point_constr P I)
           {e₂ e₃ : endpoint coh_2gr_point_constr P I}
           (h : homot_endpoint
                  coh_2gr_paths_lhs
                  coh_2gr_paths_rhs
                  (c P (tt : unit_one_type))
                  (c P (tt : unit_one_type))
                  e₂
                  e₃)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
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
           {e₁ e₂ : endpoint coh_2gr_point_constr P I}
           (e₃ : endpoint coh_2gr_point_constr P I)
           (h : homot_endpoint
                  coh_2gr_paths_lhs
                  coh_2gr_paths_rhs
                  (c P (tt : unit_one_type))
                  (c P (tt : unit_one_type))
                  e₁
                  e₂)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
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

Definition coh_2gr_homots_point_lhs
           (i : coh_2gr_homots)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
      (c (coh_2gr_homots_point_arg i) (tt : unit_one_type))
      (c (coh_2gr_homots_point_arg i) (tt : unit_one_type))
      (coh_2gr_homots_point_left_endpoint i)
      (coh_2gr_homots_point_right_endpoint i).
Proof.
  induction i.
  - (* inv_adj_triangle_l *)
    exact (trans_e
             (rwhisker_endpoint
                _
                (rinv_homot_endpoint (id_e _ _)))
             (trans_e
                (inv_e (assoc_homot_endpoint _ _ _))
                (lwhisker_endpoint
                   _
                   (linv_homot_endpoint (id_e _ _))))).
  - (* inv_adj_triangle_r *)
    exact (trans_e
             (lwhisker_endpoint
                _
                (rinv_homot_endpoint (id_e _ _)))
             (trans_e
                (assoc_homot_endpoint _ _ _)
                (rwhisker_endpoint
                   _
                   (linv_homot_endpoint (id_e _ _))))).
  - (* triangle *)
    exact (lwhisker_endpoint
             (π₁ I I)
             (lunit_homot_endpoint _)).
  - (* pentagon *)
    exact (trans_e
             (assoc_homot_endpoint _ _ _)
             (assoc_homot_endpoint _ _ _)).
Defined.

Definition coh_2gr_homots_point_rhs
           (i : coh_2gr_homots)
  : homot_endpoint
      coh_2gr_paths_lhs
      coh_2gr_paths_rhs
      (c (coh_2gr_homots_point_arg i) (tt : unit_one_type))
      (c (coh_2gr_homots_point_arg i) (tt : unit_one_type))
      (coh_2gr_homots_point_left_endpoint i)
      (coh_2gr_homots_point_right_endpoint i).
Proof.
  induction i.
  - (* inv_adj_triangle_l *)
    exact (trans_e
             (lunit_homot_endpoint _)
             (inv_e (runit_homot_endpoint _))).
  - (* inv_adj_triangle_r *)
    exact (trans_e
             (runit_homot_endpoint _)
             (inv_e (lunit_homot_endpoint _))).
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

Definition coh_2gr_signature
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact coh_2gr_point_constr.
  - exact coh_2gr_paths.
  - exact coh_2gr_paths_args.
  - exact coh_2gr_paths_lhs.
  - exact coh_2gr_paths_rhs.
  - exact coh_2gr_homots.
  - exact coh_2gr_homots_point_arg.
  - exact (λ _, C unit_one_type).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact coh_2gr_homots_point_left_endpoint.
  - exact coh_2gr_homots_point_right_endpoint.
  - exact coh_2gr_homots_point_lhs.
  - exact coh_2gr_homots_point_rhs.
Defined.

Section Coherent2GroupAlgebraProjections.
  Variable (X : hit_algebra_one_types coh_2gr_signature).
  
  Definition coh_2gr_carrier
    : one_type
    := pr111 X.

  Definition coh_2gr_unit
    : coh_2gr_carrier
    := pr211 X (inl (inl tt)).

  Definition coh_2gr_inv
             (x : coh_2gr_carrier)
    : coh_2gr_carrier
    := pr211 X (inl (inr x)).

  Definition coh_2gr_mult
             (x y : coh_2gr_carrier)
    : coh_2gr_carrier
    := pr211 X (inr (x ,, y)).

  Definition coh_2gr_lunit
             (x : coh_2gr_carrier)
    : coh_2gr_mult coh_2gr_unit x
      =
      x
    := pr21 X lunit x.
  
  Definition coh_2gr_runit
             (x : coh_2gr_carrier)
    : coh_2gr_mult x coh_2gr_unit
      =
      x
    := pr21 X runit x.

  Definition coh_2gr_linv
             (x : coh_2gr_carrier)
    : coh_2gr_mult (coh_2gr_inv x) x
      =
      coh_2gr_unit
    := pr21 X linv x.

  Definition coh_2gr_rinv
             (x : coh_2gr_carrier)
    : coh_2gr_unit
      =
      coh_2gr_mult x (coh_2gr_inv x)
    := pr21 X rinv x.

  Definition coh_2gr_assoc
             (x y z : coh_2gr_carrier)
    : coh_2gr_mult x (coh_2gr_mult y z)
      =
      coh_2gr_mult (coh_2gr_mult x y) z
    := pr21 X massoc ((x ,, y) ,, z).

  Definition coh_2gr_inv_adj_triangle_l
             (x : coh_2gr_carrier)
    : maponpaths
        (λ z, coh_2gr_mult z x)
        (coh_2gr_rinv x)
      @ !(coh_2gr_assoc _ _ _)
      @ maponpaths
          (λ z, coh_2gr_mult x z)
          (coh_2gr_linv x)
      =
      coh_2gr_lunit x @ !(coh_2gr_runit x).
  Proof.
    refine (_ @ pr2 X inv_adj_triangle_l x (idpath tt) @ _).
    - unfold coh_2gr_mult, coh_2gr_linv, coh_2gr_rinv, coh_2gr_assoc, coh_2gr_inv.
      simpl.
      rewrite !pathscomp0rid.
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply ap_pair_l.
          }
          apply (maponpathscomp (λ q, q ,, x) inr).
        }
        apply (maponpathscomp (λ q, inr (q ,, x))).
      }
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply ap_pair_r.
        }
        apply (maponpathscomp (λ q, x ,, q) inr).
      }
      apply (maponpathscomp (λ q, inr (x ,, q))).
    - unfold coh_2gr_lunit, coh_2gr_runit.
      simpl.
      rewrite !pathscomp0rid.
      apply idpath.
  Qed.
  
  Definition coh_2gr_inv_adj_triangle_r
             (x : coh_2gr_carrier)
    : maponpaths
        (λ z, coh_2gr_mult _ z)
        (coh_2gr_rinv x)
      @ coh_2gr_assoc _ _ _
      @ maponpaths
          (λ z, coh_2gr_mult z _)
          (coh_2gr_linv x)
      =
      coh_2gr_runit (coh_2gr_inv x) @ !(coh_2gr_lunit (coh_2gr_inv x)).
  Proof.
    refine (_ @ pr2 X inv_adj_triangle_r x (idpath tt) @ _).
    - unfold coh_2gr_mult, coh_2gr_linv, coh_2gr_rinv, coh_2gr_assoc, coh_2gr_inv.
      simpl.
      rewrite !pathscomp0rid.
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply ap_pair_r.
          }
          apply (maponpathscomp _ inr).
        }
        apply (maponpathscomp (λ q, inr ((pr211 X) (inl (inr x)),, q)) (pr211 X)).
      }
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply ap_pair_l.
        }
        apply (maponpathscomp (λ q, q ,, _) inr).
      }
      apply (maponpathscomp (λ q, inr (q ,, _))).
    - unfold coh_2gr_lunit, coh_2gr_runit.
      simpl.
      rewrite !pathscomp0rid.
      apply idpath.
  Qed.
  
  Definition coh_2gr_triangle
             (x y : coh_2gr_carrier)
    : maponpaths
        (λ z, coh_2gr_mult x z)
        (coh_2gr_lunit y)
      =
      (coh_2gr_assoc _ _ _)
      @ maponpaths
          (λ z, coh_2gr_mult z y)
          (coh_2gr_runit x).
  Proof.
    refine (_ @ pr2 X triangle (x ,, y) (idpath tt) @ _).
    - unfold coh_2gr_mult, coh_2gr_lunit.
      simpl.
      rewrite !pathscomp0rid.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply ap_pair_r.
        }
        apply maponpathscomp.
      }
      exact (maponpathscomp (λ q, inr (x,, q)) (pr211 X)  (pr21 X lunit y)).
    - unfold coh_2gr_assoc, coh_2gr_runit.
      simpl.
      rewrite !pathscomp0rid.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply ap_pair_l.
        }
        exact (maponpathscomp (λ q, q ,, y) inr (pr21 X runit x)).
      }
      exact (maponpathscomp (λ q, inr (q,, y)) (pr211 X) (pr21 X runit x)).
  Qed.

  Definition coh_2gr_pentagon
             (w x y z : coh_2gr_carrier)
    : coh_2gr_assoc w x (coh_2gr_mult y z)
      @ coh_2gr_assoc (coh_2gr_mult w x) y z
      =
      maponpaths
        (λ q, coh_2gr_mult w q)
        (coh_2gr_assoc x y z)
      @ coh_2gr_assoc w (coh_2gr_mult x y) z
      @ maponpaths
          (λ q, coh_2gr_mult q z)
          (coh_2gr_assoc w x y).
  Proof.
    refine (_ @ pr2 X pentagon (((w ,, x) ,, y) ,, z) (idpath tt) @ _).
    - simpl.
      rewrite !pathscomp0rid.
      apply idpath.
    - simpl.
      rewrite !pathscomp0rid.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply ap_pair_r.
          }
          apply maponpathscomp.
        }
        apply (maponpathscomp (λ q, inr (w ,, q)) (pr211 X)).
      }
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply ap_pair_l.
        }
        apply (maponpathscomp (λ q, q ,, z) inr).
      }
      apply (maponpathscomp (λ q, inr (q ,, z)) (pr211 X)).
  Qed.
End Coherent2GroupAlgebraProjections.
