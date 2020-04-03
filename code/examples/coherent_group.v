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

(** The signature *)
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

(**
Projections.
We define projections for both path algebras and algebras.
This allowing reusing results for the builder.
 *)
Section Coherent2GroupPathAlgebraProjections.
  Variable (X : hit_path_algebra_one_types coh_2gr_signature).
  
  Definition coh_2gr_carrier_PA
    : one_type
    := pr11 X.

  Definition coh_2gr_unit_PA
    : coh_2gr_carrier_PA
    := pr21 X (inl (inl tt)).

  Definition coh_2gr_inv_PA
             (x : coh_2gr_carrier_PA)
    : coh_2gr_carrier_PA
    := pr21 X (inl (inr x)).

  Definition coh_2gr_mult_PA
             (x y : coh_2gr_carrier_PA)
    : coh_2gr_carrier_PA
    := pr21 X (inr (x ,, y)).

  Definition coh_2gr_lunit_PA
             (x : coh_2gr_carrier_PA)
    : coh_2gr_mult_PA coh_2gr_unit_PA x
      =
      x
    := pr2 X lunit x.
  
  Definition coh_2gr_runit_PA
             (x : coh_2gr_carrier_PA)
    : coh_2gr_mult_PA x coh_2gr_unit_PA
      =
      x
    := pr2 X runit x.

  Definition coh_2gr_linv_PA
             (x : coh_2gr_carrier_PA)
    : coh_2gr_mult_PA (coh_2gr_inv_PA x) x
      =
      coh_2gr_unit_PA
    := pr2 X linv x.

  Definition coh_2gr_rinv_PA
             (x : coh_2gr_carrier_PA)
    : coh_2gr_unit_PA
      =
      coh_2gr_mult_PA x (coh_2gr_inv_PA x)
    := pr2 X rinv x.

  Definition coh_2gr_assoc_PA
             (x y z : coh_2gr_carrier_PA)
    : coh_2gr_mult_PA x (coh_2gr_mult_PA y z)
      =
      coh_2gr_mult_PA (coh_2gr_mult_PA x y) z
    := pr2 X massoc ((x ,, y) ,, z).

  Definition coh_2gr_inv_adj_triangle_l_l
             (x : coh_2gr_carrier_PA)
    : maponpaths (λ z, coh_2gr_mult_PA z x) (coh_2gr_rinv_PA x)
      @ !(coh_2gr_assoc_PA x (coh_2gr_inv_PA x) x)
      @ maponpaths (λ z, coh_2gr_mult_PA x z) (coh_2gr_linv_PA x)
      =
      sem_homot_endpoint_one_types
        (homot_left_path coh_2gr_signature inv_adj_triangle_l) 
        (pr1 X) (pr2 X)
        x (idpath tt).
  Proof.
    unfold coh_2gr_mult_PA, coh_2gr_linv_PA, coh_2gr_rinv_PA ;
    unfold coh_2gr_assoc_PA, coh_2gr_inv_PA.
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
  Qed.

  Definition coh_2gr_inv_adj_triangle_l_r
             (x : coh_2gr_carrier_PA)
    : sem_homot_endpoint_one_types
        (homot_right_path coh_2gr_signature inv_adj_triangle_l) 
        (pr1 X) (pr2 X)
        x (idpath tt)
      = coh_2gr_lunit_PA x @ !(coh_2gr_runit_PA x).
  Proof.
    unfold coh_2gr_lunit_PA, coh_2gr_runit_PA.
    simpl.
    rewrite !pathscomp0rid.
    apply idpath.
  Qed.

  Definition coh_2gr_inv_adj_triangle_r_l
             (x : coh_2gr_carrier_PA)
    : maponpaths (λ z, coh_2gr_mult_PA (coh_2gr_inv_PA x) z) (coh_2gr_rinv_PA x)
      @ coh_2gr_assoc_PA (coh_2gr_inv_PA x) x (coh_2gr_inv_PA x)
      @ maponpaths (λ z, coh_2gr_mult_PA z (coh_2gr_inv_PA x)) (coh_2gr_linv_PA x)
      =
      sem_homot_endpoint_one_types
        (homot_left_path coh_2gr_signature inv_adj_triangle_r) 
        (pr1 X) (pr2 X)
        x (idpath tt).
  Proof.
    unfold coh_2gr_mult_PA, coh_2gr_linv_PA, coh_2gr_rinv_PA ;
    unfold coh_2gr_assoc_PA, coh_2gr_inv_PA.
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
      apply (maponpathscomp (λ q, inr ((pr21 X) (inl (inr x)),, q)) (pr21 X)).
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
  Qed.

  Definition coh_2gr_inv_adj_triangle_r_r
             (x : coh_2gr_carrier_PA)
    : sem_homot_endpoint_one_types
        (homot_right_path coh_2gr_signature inv_adj_triangle_r) 
        (pr1 X) (pr2 X)
        x
        (idpath tt)
      =
      coh_2gr_runit_PA (coh_2gr_inv_PA x)
      @ !(coh_2gr_lunit_PA (coh_2gr_inv_PA x)).
  Proof.
    unfold coh_2gr_lunit_PA, coh_2gr_runit_PA.
    simpl.
    rewrite !pathscomp0rid.
    apply idpath.
  Qed.

  Definition coh_2gr_triangle_l
             (x y : coh_2gr_carrier_PA)
    : maponpaths (λ z, coh_2gr_mult_PA x z) (coh_2gr_lunit_PA y)
      =
      sem_homot_endpoint_one_types
        (homot_left_path coh_2gr_signature triangle) 
        (pr1 X) (pr2 X)
        (x,, y) (idpath tt).
  Proof.
    unfold coh_2gr_mult_PA, coh_2gr_lunit_PA.
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
    exact (maponpathscomp (λ q, inr (x,, q)) (pr21 X)  (pr2 X lunit y)).
  Qed.

  Definition coh_2gr_triangle_r
             (x y : coh_2gr_carrier_PA)
    : sem_homot_endpoint_one_types
        (homot_right_path coh_2gr_signature triangle) 
        (pr1 X) (pr2 X)
        (x,, y) (idpath tt)
      =
      coh_2gr_assoc_PA x coh_2gr_unit_PA y
      @ maponpaths (λ z, coh_2gr_mult_PA z y) (coh_2gr_runit_PA x).
  Proof.
    unfold coh_2gr_assoc_PA, coh_2gr_runit_PA.
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
      exact (maponpathscomp (λ q, q ,, y) inr (pr2 X runit x)).
    }
    exact (maponpathscomp (λ q, inr (q,, y)) (pr21 X) (pr2 X runit x)).
  Qed.

  Definition coh_2gr_pentagon_l
             (w x y z : coh_2gr_carrier_PA)
    : coh_2gr_assoc_PA w x (coh_2gr_mult_PA y z)
      @ coh_2gr_assoc_PA (coh_2gr_mult_PA w x) y z
      =
      sem_homot_endpoint_one_types
        (homot_left_path coh_2gr_signature pentagon) 
        (pr1 X) (pr2 X)
        (((w,, x),, y),, z) (idpath tt).
  Proof.
    simpl.
    rewrite !pathscomp0rid.
    apply idpath.
  Qed.

  Definition coh_2gr_pentagon_r
             (w x y z : coh_2gr_carrier_PA)
    : sem_homot_endpoint_one_types
        (homot_right_path coh_2gr_signature pentagon) 
        (pr1 X) (pr2 X)
        (((w,, x),, y),, z) (idpath tt)
      =
      maponpaths (λ q, coh_2gr_mult_PA w q) (coh_2gr_assoc_PA x y z)
      @ coh_2gr_assoc_PA w (coh_2gr_mult_PA x y) z
      @ maponpaths (λ q, coh_2gr_mult_PA q z) (coh_2gr_assoc_PA w x y).
  Proof.
    simpl.
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
      apply (maponpathscomp (λ q, inr (w ,, q)) (pr21 X)).
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
    apply (maponpathscomp (λ q, inr (q ,, z)) (pr21 X)).
  Qed.
End Coherent2GroupPathAlgebraProjections.

Section Coherent2GroupAlgebraProjections.
  Variable (X : hit_algebra_one_types coh_2gr_signature).
  
  Definition coh_2gr_carrier
    : one_type
    := coh_2gr_carrier_PA (pr1 X).

  Definition coh_2gr_unit
    : coh_2gr_carrier
    := coh_2gr_unit_PA (pr1 X).

  Definition coh_2gr_inv
             (x : coh_2gr_carrier)
    : coh_2gr_carrier
    := coh_2gr_inv_PA (pr1 X) x.

  Definition coh_2gr_mult
             (x y : coh_2gr_carrier)
    : coh_2gr_carrier
    := coh_2gr_mult_PA (pr1 X) x y.

  Definition coh_2gr_lunit
             (x : coh_2gr_carrier)
    : coh_2gr_mult coh_2gr_unit x
      =
      x
    := coh_2gr_lunit_PA (pr1 X) x.
  
  Definition coh_2gr_runit
             (x : coh_2gr_carrier)
    : coh_2gr_mult x coh_2gr_unit
      =
      x
    := coh_2gr_runit_PA (pr1 X) x.

  Definition coh_2gr_linv
             (x : coh_2gr_carrier)
    : coh_2gr_mult (coh_2gr_inv x) x
      =
      coh_2gr_unit
    := coh_2gr_linv_PA (pr1 X) x.

  Definition coh_2gr_rinv
             (x : coh_2gr_carrier)
    : coh_2gr_unit
      =
      coh_2gr_mult x (coh_2gr_inv x)
    := coh_2gr_rinv_PA (pr1 X) x.

  Definition coh_2gr_assoc
             (x y z : coh_2gr_carrier)
    : coh_2gr_mult x (coh_2gr_mult y z)
      =
      coh_2gr_mult (coh_2gr_mult x y) z
    := coh_2gr_assoc_PA (pr1 X) x y z.

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
    - exact (coh_2gr_inv_adj_triangle_l_l _ x).
    - exact (coh_2gr_inv_adj_triangle_l_r _ x).
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
    - exact (coh_2gr_inv_adj_triangle_r_l _ x).
    - exact (coh_2gr_inv_adj_triangle_r_r _ x).
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
    - exact (coh_2gr_triangle_l _ x y).
    - exact (coh_2gr_triangle_r _ x y).
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
    - exact (coh_2gr_pentagon_l _ w x y z).
    - exact (coh_2gr_pentagon_r _ w x y z).
  Qed.
End Coherent2GroupAlgebraProjections.

(** Builder *)
Section Coherent2GroupBuilder.
  Variable (A : one_type)
           (e : A)
           (i : A → A)
           (m : A → A → A)
           (unitl_m : ∏ (x : A), m e x = x)
           (unitr_m : ∏ (x : A), m x e = x)
           (invl_m : ∏ (x : A), m (i x) x = e)
           (invr_m : ∏ (x : A), e = m x (i x))
           (assoc_m : ∏ (x y z : A), m x (m y z) = m (m x y) z)
           (m_invt_l : ∏ (x : A),
                       maponpaths (λ z, m z x) (invr_m x)
                       @ !(assoc_m _ _ _)
                       @ maponpaths (λ z, m x z) (invl_m x)
                       =
                       unitl_m x @ !(unitr_m x))
           (m_invt_r : ∏ (x : A),
                       maponpaths (λ z, m _ z) (invr_m x)
                       @ assoc_m _ _ _
                       @ maponpaths (λ z, m z _) (invl_m x)
                       =
                       unitr_m (i x) @ !(unitl_m (i x)))
           (triangle_m : ∏ (x y : A),
                         maponpaths (λ z, m x z) (unitl_m y)
                         =
                         (assoc_m _ _ _)
                         @ maponpaths (λ z, m z y) (unitr_m x))
           (pentagon_m : ∏ (w x y z : A),
                         assoc_m w x (m y z)
                         @ assoc_m (m w x) y z
                         =
                         maponpaths (λ q, m w q) (assoc_m x y z)
                         @ assoc_m w (m x y) z
                         @ maponpaths (λ q, m q z) (assoc_m w x y)).

  Local Definition make_2gr_prealgebra
    : hit_prealgebra_one_types coh_2gr_signature.
  Proof.
    use make_hit_prealgebra.
    - exact A.
    - apply one_type_isofhlevel.
    - intro x ; induction x as [x | x].
      + induction x as [ | x].
        * exact e.
        * exact (i x).
      + exact (m (pr1 x) (pr2 x)).
  Defined.
  
  Local Definition make_2gr_path_algebra
    : hit_path_algebra_one_types coh_2gr_signature.
  Proof.
    use make_hit_path_algebra.
    - exact make_2gr_prealgebra.
    - intros j x.
      induction j.
      + (* unitl *)
        apply unitl_m.
      + (* unitr *)
        apply unitr_m.
      + (* invl *)
        apply invl_m.
      + (* invr *)
        apply invr_m.
      + (* assoc *)
        apply assoc_m.
  Defined.

  Definition make_2gr_path_algebra_is_algebra
    : is_hit_algebra_one_types coh_2gr_signature make_2gr_path_algebra.
  Proof.
    intros j x p.
    induction j.
    - (* inv_adj_triangle_l *)
      refine (_ @ m_invt_l x @ _).
      + exact (!(coh_2gr_inv_adj_triangle_l_l _ x)).
      + exact (!(coh_2gr_inv_adj_triangle_l_r _ x)).
    - (* inv_adj_triangle_r *)
      refine (_ @ m_invt_r x @ _).
      + exact (!(coh_2gr_inv_adj_triangle_r_l _ x)).
      + exact (!(coh_2gr_inv_adj_triangle_r_r _ x)).
    - (* triangle *)
      refine (_ @ triangle_m (pr1 x) (pr2 x) @ _).
      + exact (!(coh_2gr_triangle_l _ (pr1 x) (pr2 x))).
      + exact (!(coh_2gr_triangle_r _ (pr1 x) (pr2 x))).
    - (* pentagon *)
      refine (_ @ pentagon_m (pr111 x) (pr211 x) (pr21 x) (pr2 x) @ _).
      + exact (!(coh_2gr_pentagon_l _ (pr111 x) (pr211 x) (pr21 x) (pr2 x))).
      + exact (!(coh_2gr_pentagon_r _ (pr111 x) (pr211 x) (pr21 x) (pr2 x))).
  Qed.
  
  Definition make_2gr_algebra
    : hit_algebra_one_types coh_2gr_signature.
  Proof.
    use make_algebra.
    - exact make_2gr_path_algebra.
    - exact make_2gr_path_algebra_is_algebra.
  Defined.
End Coherent2GroupBuilder.

(** The loop space of a 2-type is a coherent 2-group *)
Definition loop_space_2gr
           {X : UU}
           (HX : isofhlevel 4 X)
           (x : X)
  : hit_algebra_one_types coh_2gr_signature.
Proof.
  use make_2gr_algebra.
  - use make_one_type.
    + exact (x = x).
    + exact (HX x x).
  - exact (idpath x).
  - exact (λ p, !p).
  - exact (λ p q, p @ q).
  - exact (λ p, idpath p).
  - exact pathscomp0rid.
  - exact pathsinv0l.
  - exact (λ p, !(pathsinv0r p)).
  - exact path_assoc.
  - simpl.
    intro p ; induction p.
    apply idpath.
  - intro p ; induction p.
    apply idpath.
  - intro p ; induction p.
    exact (λ _, idpath _).
  - intro p ; induction p.
    intro p ; induction p.
    exact (λ _ _, idpath _).
Defined.

(**
The automorphism 2-group of `X`.
Assuming univalence, this is just the loopspace of the type of 1-types with basepoint `X`.
Here we construct it without assuming univalence.
 *)
Local Open Scope weq.

(**
We first give some principles to construct equalities between weak equivalences.
In addition, we prove some properties about them.
 *)
Definition path_isweq
           {X Y : UU}
           {f : X → Y}
           (Hf₁ Hf₂ : isweq f)
  : Hf₁ = Hf₂.
Proof.
  apply isapropisweq.
Defined.

Definition path_weq'
           {X Y : UU}
           {f g : X ≃ Y}
           (p : pr1 f = pr1 g)
  : f = g.
Proof.
  induction f as [f Hf], g as [g Hg] ; simpl in *.
  induction p.
  refine (maponpaths (λ z, f ,, z) _).
  apply path_isweq.
Defined.

Definition path_weq
           {X Y : UU}
           {f g : X ≃ Y}
           (p : ∏ (x : X), f x = g x)
  : f = g.
Proof.
  apply path_weq'.
  use funextsec.
  exact p.
Defined.

Definition inv_path_weq'
           {X Y : UU}
           {f g : X ≃ Y}
           (p : pr1 f = pr1 g)
  : !(path_weq' p) = path_weq' (!p).
Proof.
  induction f as [f Hf] ; induction g as [g Hg] ; simpl in *.
  induction p.
  simpl.
  etrans.
  {
    refine (!_).
    apply maponpathsinv0.
  }
  apply maponpaths.
  apply isapropisweq.
Defined.

Definition comp_path_weq'
           {X Y : UU}
           {f g h : X ≃ Y}
           (p : pr1 f = pr1 g)
           (q : pr1 g = pr1 h)
  : path_weq' p @ path_weq' q = path_weq' (p @ q).
Proof.
  induction f as [f Hf]
  ; induction g as [g Hg]
  ; induction h as [h Hh]
  ; simpl in *.
  induction p ; induction q ; simpl.
  etrans.
  {
    refine (!_).
    apply maponpathscomp0.
  }
  apply maponpaths.
  apply isapropisweq.
Defined.

Definition precomp_path_weq'
           {X Y Z : UU}
           (f : X ≃ Y)
           {g h : Y ≃ Z}
           (p : pr1 g = pr1 h)
  : maponpaths
      (λ z, z ∘ f)
      (path_weq' p)
    =
    @path_weq' X Z (g ∘ f) (h ∘ f) (maponpaths (λ z, z ∘ pr1 f)%functions p).
Proof.
  induction g as [g Hg]
  ; induction h as [h Hh]
  ; simpl in *.
  induction p ; simpl.
  etrans.
  {
    apply maponpathscomp.
  }
  etrans.
  {
    refine (!_).
    exact (maponpathscomp _ (λ z, _ ,, z) _).
  }
  simpl.
  apply maponpaths.
  apply isapropisweq.
Qed.

Definition postcomp_path_weq'
           {X Y Z : UU}
           {f g : X ≃ Y}
           (h : Y ≃ Z)
           (p : pr1 f = pr1 g)
  : maponpaths
      (λ z, h ∘ z)
      (path_weq' p)
    =
    @path_weq' X Z (h ∘ f) (h ∘ g) (maponpaths (λ z, (λ x, h(z x))) p).
Proof.
  induction f as [f Hf]
  ; induction g as [g Hg]
  ; simpl in *.
  induction p ; simpl.
  etrans.
  {
    apply (maponpathscomp _ (λ z, h ∘ z)).
  }
  unfold funcomp, weqcomp, make_weq ; simpl.
  etrans.
  {
    refine (!_).
    exact (maponpathscomp
             (λ z, twooutof3c f h z (pr2 h))
             (λ z, (λ q, h(f q)) ,, z)
             _).
  }
  simpl.
  apply maponpaths.
  apply isapropisweq.
Qed.

(** Necessary lemmas about function extensionality *)
Definition funextsec_idpath
           {X Y : UU}
           (f : X → Y)
  : funextsec _ _ _ (λ x, idpath (f x)) = idpath f.
Proof.
  refine (_ @ funextsec_toforallpaths _).
  apply idpath.
Qed.

Definition inv_toforallpaths
           {X : UU}
           {Y : X → UU}
           {f g : ∏ (x : X), Y x}
           (p : f = g)
  : (λ x, !(toforallpaths _ _ _ p x)) = toforallpaths _ _ _ (!p).
Proof.
  induction p.
  apply idpath.
Qed.

Definition inv_funextsec
           {X Y : UU}
           {f g : X → Y}
           (p : ∏ (x : X), f x = g x)
  : !(funextsec _ _ _ p) = funextsec _ _ _ (λ x, !(p x)).
Proof.
  refine (!(funextsec_toforallpaths _) @ _).
  apply maponpaths.
  refine (!(inv_toforallpaths (funextsec _ _ _ p)) @ _) ; simpl.
  use funextsec ; intro x.
  apply maponpaths.
  exact (eqtohomot (toforallpaths_funextsec p) x).
Qed.

Definition comp_toforallpaths
           {X : UU}
           {Y : X → UU}
           {f g h : ∏ (x : X), Y x}
           (p : f = g) (q : g = h)
  : toforallpaths _ _ _ (p @ q)
    =
    (λ x, toforallpaths _ _ _ p x @ toforallpaths _ _ _ q x).
Proof.
  induction p, q.
  apply idpath.
Qed.

Definition comp_funextsec
           {X Y : UU}
           {f g h : X → Y}
           (p : ∏ (x : X), f x = g x)
           (q : ∏ (x : X), g x = h x)
  : funextsec _ _ _ p @ funextsec _ _ _ q
    =
    funextsec _ _ _ (λ x, p x @ q x).
Proof.
  refine (!(funextsec_toforallpaths _) @ _).
  apply maponpaths.
  refine (comp_toforallpaths _ _ @ _).
  use funextsec ; intro x ; simpl.
  rewrite !toforallpaths_funextsec.
  apply idpath.
Qed.

Definition precomp_toforallpaths
           {X Y Z : UU}
           (f : X → Y)
           {g h : Y → Z}
           (p : g = h)
  : toforallpaths
      _ _ _
      (maponpaths (λ z : Y → Z, (z ∘ f)%functions) p)
    =
    (λ x, toforallpaths _ _ _ p (f x)).
Proof.
  induction p.
  apply idpath.
Qed.

Definition precomp_funextsec
           {X Y Z : UU}
           (f : X → Y)
           {g h : Y → Z}
           (p : ∏ (y : Y), g y = h y)
  : maponpaths
      (λ z : Y → Z, (z ∘ f)%functions)
      (funextsec _ _ _ p)
    =
    funextsec _ _ _ (λ x : X, p (f x)).
Proof.
  refine (!(funextsec_toforallpaths _) @ _).
  apply maponpaths.
  refine (precomp_toforallpaths f (funextsec _ _ _ p) @ _).
  use funextsec ; intro x.
  exact (eqtohomot (toforallpaths_funextsec _) (f x)).
Qed.

Definition postcomp_toforallpaths
           {X Y Z : UU}
           {f g : X → Y}
           (h : Y → Z)
           (p : f = g)
  : toforallpaths
      _ _ _
      (maponpaths (λ q : X → Y, (λ x, h(q x))) p)
    =
    (λ x, maponpaths h (toforallpaths _ _ _ p x)).
Proof.
  induction p.
  apply idpath.
Qed.

Definition postcomp_funext
           {X Y Z : UU}
           {f g : X → Y}
           (h : Y → Z)
           (p : ∏ (x : X), f x = g x)
  : maponpaths
      (λ (z : X → Y) (x : X), h (z x))
      (funextsec _ _ _ p)
    =
    funextsec _ _ _ (λ x : X, maponpaths h (p x)).
Proof.
  refine (!(funextsec_toforallpaths _) @ _).
  apply maponpaths.
  refine (postcomp_toforallpaths h _ @ _).
  use funextsec ; intro x ; simpl.
  apply maponpaths.
  exact (eqtohomot (toforallpaths_funextsec p) x).
Qed.  

(** The lemmas on `path_weq` we need *)
Definition inv_path_weq
           {X Y : UU}
           {f g : X ≃ Y}
           (p : ∏ (x : X), f x = g x)
  : !(path_weq p) = path_weq (λ x, !(p x)).
Proof.
  refine (inv_path_weq' _ @ _).
  unfold path_weq ; apply maponpaths.
  apply inv_funextsec.
Qed.

Definition comp_path_weq
           {X Y : UU}
           {f g h : X ≃ Y}
           (p : ∏ (x : X), f x = g x)
           (q : ∏ (x : X), g x = h x)
  : path_weq p @ path_weq q
    =
    path_weq (λ x, p x @ q x).
Proof.
  refine (comp_path_weq' _ _ @ _).
  unfold path_weq ; apply maponpaths.
  apply comp_funextsec.
Qed.

Definition precomp_path_weq
           {X Y Z : UU}
           (f : X ≃ Y)
           {g h : Y ≃ Z}
           (p : ∏ (y : Y), g y = h y)
  : maponpaths
      (λ z, z ∘ f)
      (path_weq p)
    =
    @path_weq X Z (g ∘ f) (h ∘ f) (λ x, p (f x)).
Proof.
  refine (precomp_path_weq' _ _ @ _).
  unfold path_weq.
  apply maponpaths.
  exact (precomp_funextsec f p).
Qed.

Definition postcomp_path_weq
           {X Y Z : UU}
           {f g : X ≃ Y}
           (h : Y ≃ Z)
           (p : ∏ (x : X), f x = g x)
  : maponpaths
      (λ z, h ∘ z)
      (path_weq p)
    =
    @path_weq X Z (h ∘ f) (h ∘ g) (λ x, maponpaths h (p x)).
Proof.
  refine (postcomp_path_weq' _ _ @ _).
  unfold path_weq.
  apply maponpaths.
  exact (postcomp_funext h p).
Qed.
           
Definition homotweq
           {X Y : UU}
           {f g : X ≃ Y}
           {p q : ∏ (x : X), f x = g x}
           (r : ∏ (x : X), p x = q x)
  : path_weq p = path_weq q.
Proof.
  assert (p = q) as H.
  {
    use funextsec.
    exact r.
  }
  induction H.
  apply idpath.
Defined.

(**
The laws to show that weak equivalences on `X` form a coherent weak 2-group.
 *)
Definition weq_id_l
           {X : UU}
           (f : X ≃ X)
  : f ∘ idweq X = f.
Proof.
  use path_weq.
  exact (λ _, idpath _).
Defined.

Definition weq_id_r
           {X : UU}
           (f : X ≃ X)
  : idweq X ∘ f = f.
Proof.
  use path_weq.
  exact (λ _, idpath _).
Defined.

Definition weq_inv_l
           {X : UU}
           (f : X ≃ X)
  : f ∘ invweq f = idweq X.
Proof.
  use path_weq.
  intro x ; simpl.
  exact (homotweqinvweq f x).
Defined.

Definition weq_inv_r
           {X : UU}
           (f : X ≃ X)
  : idweq X = invweq f ∘ f.
Proof.
  use path_weq.
  intro x ; simpl.
  exact (!(homotinvweqweq f x)).
Defined.

Definition weq_assoc
           {X : UU}
           (f g h : X ≃ X)
  : (h ∘ g) ∘ f = h ∘ (g ∘ f).
Proof.
  use path_weq.
  exact (λ _, idpath _).
Defined.

Definition weq_inv_triangle_l
           {X : UU}
           (f : X ≃ X)
  : maponpaths
      (λ z : X ≃ X, f ∘ z)
      (weq_inv_r f)
    @ !(weq_assoc f (invweq f) f)
    @ maponpaths (λ z : X ≃ X, z ∘ f) (weq_inv_l f)
    =
    weq_id_l f @ ! weq_id_r f.
Proof.
  unfold weq_inv_r, weq_assoc, weq_inv_l.
  etrans.
  {
    etrans.
    {
      apply maponpaths_2.
      apply postcomp_path_weq.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply inv_path_weq.
      }
      etrans.
      {
        apply maponpaths.
        apply precomp_path_weq.
      }
      apply comp_path_weq.
    }
    apply comp_path_weq.
  }
  unfold weq_id_l, weq_id_r.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply inv_path_weq.
  }
  etrans.
  {
    apply comp_path_weq.
  }
  apply homotweq.
  intros x ; simpl.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    exact (!(homotweqinvweqweq f x)).
  }
  etrans.
  {
    refine (!_).
    apply maponpathscomp0.
  }
  etrans.
  {
    apply maponpaths.
    apply pathsinv0l.
  }
  apply idpath.
Qed.

Definition weq_inv_triangle_r
           {X : UU}
           (f : X ≃ X)
  : maponpaths (λ z : X ≃ X, z ∘ invweq f) (weq_inv_r f)
    @ weq_assoc (invweq f) f (invweq f)
    @ maponpaths (λ z : X ≃ X, invweq f ∘ z) (weq_inv_l f)
    =
    weq_id_r (invweq f) @ ! weq_id_l (invweq f).
Proof.
  unfold weq_inv_r, weq_assoc, weq_inv_l.
  etrans.
  {
    etrans.
    {
      apply maponpaths_2.
      apply precomp_path_weq.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply postcomp_path_weq.
      }
      apply comp_path_weq.
    }
    apply comp_path_weq.
  }
  unfold weq_id_l, weq_id_r.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply inv_path_weq.
  }
  etrans.
  {
    apply comp_path_weq.
  }
  apply homotweq.
  intros x ; simpl.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply homotweqweqinvweq.
  }
  apply pathsinv0l.
Qed.

Definition weq_triangle
           {X : UU}
           (f g : X ≃ X)
  : maponpaths (λ z : X ≃ X, z ∘ f) (weq_id_l g) =
    weq_assoc f (idweq X) g
    @ maponpaths (λ z : X ≃ X, g ∘ z) (weq_id_r f).
Proof.
  etrans.
  {
    apply precomp_path_weq.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply postcomp_path_weq.
  }
  etrans.
  {
    apply comp_path_weq.
  }
  apply homotweq.
  exact (λ _, idpath _).
Qed.

Definition weq_pentagon
           {X : UU}
           (f₁ f₂ f₃ f₄ : X ≃ X)
  : weq_assoc f₁ f₂ (f₄ ∘ f₃) @ weq_assoc (f₂ ∘ f₁) f₃ f₄
    =
    maponpaths (λ q : X ≃ X, q ∘ f₁) (weq_assoc f₂ f₃ f₄)
    @ weq_assoc f₁ (f₃ ∘ f₂) f₄
    @ maponpaths (λ q : X ≃ X, f₄ ∘ q) (weq_assoc f₁ f₂ f₃).
Proof.
  etrans.
  {
    apply comp_path_weq.
  }
  refine (!_).
  etrans.
  {
    etrans.
    {
      apply maponpaths_2.
      apply precomp_path_weq.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply postcomp_path_weq.
      }
      apply comp_path_weq.
    }
    apply comp_path_weq.
  }
  apply homotweq.
  exact (λ _, idpath _).
Qed.
  
Definition aut_2gr
           (X : UU)
           (HX : isofhlevel 3 X)
  : hit_algebra_one_types coh_2gr_signature.
Proof.
  use make_2gr_algebra.
  - use make_one_type.
    + exact (X ≃ X).
    + use isofhlevelsnweqtohlevelsn.
      exact HX.
  - exact (idweq X).
  - exact invweq.
  - exact weqcomp.
  - exact weq_id_l.
  - exact weq_id_r.
  - exact weq_inv_l.
  - exact weq_inv_r.
  - exact weq_assoc.
  - exact weq_inv_triangle_l.
  - exact weq_inv_triangle_r.
  - exact weq_triangle.
  - exact weq_pentagon.
Defined.
