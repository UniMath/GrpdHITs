(**
Here we define the signature for monoidal objects.
Basically, these satisfy the same laws as monoidal categories, but instead, the laws are formulated using HIT signature.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.

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

Section MonoidalPathAlgebraProjections.
  Variable (X : hit_path_algebra_one_types monoidal_signature).

  Definition monoidal_PA_carrier
    : one_type
    := pr11 X.

  Definition monoidal_PA_unit
    : monoidal_PA_carrier
    := pr21 X (inl tt).

  Definition monoidal_PA_mult
             (x y : monoidal_PA_carrier)
    : monoidal_PA_carrier
    := pr21 X (inr (x ,, y)).

  Definition monoidal_PA_lunit
             (x : monoidal_PA_carrier)
    : monoidal_PA_mult monoidal_PA_unit x
      =
      x
    := pr2 X lunit x.
  
  Definition monoidal_PA_runit
             (x : monoidal_PA_carrier)
    : monoidal_PA_mult x monoidal_PA_unit
      =
      x
    := pr2 X runit x.

  Definition monoidal_PA_assoc
             (x y z : monoidal_PA_carrier)
    : monoidal_PA_mult x (monoidal_PA_mult y z)
      =
      monoidal_PA_mult (monoidal_PA_mult x y) z
    := pr2 X massoc ((x ,, y) ,, z).

  Definition monoidal_triangle_left
             (x y : monoidal_PA_carrier)
    : maponpaths (λ z, monoidal_PA_mult x z) (monoidal_PA_lunit y)
      =
      sem_homot_endpoint_one_types
        (homot_left_path monoidal_signature triangle) 
        (pr1 X) (pr2 X)
        (x,, y)
        (idpath tt).
  Proof.
    unfold monoidal_PA_mult, monoidal_PA_lunit.
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

  Definition monoidal_triangle_right
             (x y : monoidal_PA_carrier)
    : sem_homot_endpoint_one_types
        (homot_right_path monoidal_signature triangle) 
        (pr1 X) (pr2 X)
        (x,, y)
        (idpath tt)
      =
      monoidal_PA_assoc x monoidal_PA_unit y
      @ maponpaths (λ z, monoidal_PA_mult z y) (monoidal_PA_runit x).
  Proof.
    unfold monoidal_PA_assoc, monoidal_PA_runit.
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

  Definition monoidal_pentagon_left
             (w x y z : monoidal_PA_carrier)
    : monoidal_PA_assoc w x (monoidal_PA_mult y z)
      @ monoidal_PA_assoc (monoidal_PA_mult w x) y z
      =
      sem_homot_endpoint_one_types
        (homot_left_path monoidal_signature pentagon) 
        (pr1 X) (pr2 X)
        (((w,, x),, y),, z)
        (idpath tt).
  Proof.
    simpl.
    rewrite !pathscomp0rid.
    apply idpath.
  Qed.

  Definition monoidal_pentagon_right
             (w x y z : monoidal_PA_carrier)
    : sem_homot_endpoint_one_types
        (homot_right_path monoidal_signature pentagon) 
        (pr1 X) (pr2 X)
        (((w,, x),, y),, z)
        (idpath tt)
      =
      maponpaths (λ q, monoidal_PA_mult w q) (monoidal_PA_assoc x y z)
      @ monoidal_PA_assoc w (monoidal_PA_mult x y) z
      @ maponpaths (λ q, monoidal_PA_mult q z) (monoidal_PA_assoc w x y).
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
End MonoidalPathAlgebraProjections.

Section MonoidalAlgebraProjections.
  Variable (X : hit_algebra_one_types monoidal_signature).

  Definition monoidal_carrier
    : one_type
    := monoidal_PA_carrier (pr1 X).

  Definition monoidal_unit
    : monoidal_carrier
    := monoidal_PA_unit (pr1 X).

  Definition monoidal_mult
             (x y : monoidal_carrier)
    : monoidal_carrier
    := monoidal_PA_mult (pr1 X) x y.
  
  Definition monoidal_lunit
             (x : monoidal_carrier)
    : monoidal_mult monoidal_unit x
      =
      x
    := monoidal_PA_lunit (pr1 X) x.
  
  Definition monoidal_runit
             (x : monoidal_carrier)
    : monoidal_mult x monoidal_unit
      =
      x
    := monoidal_PA_runit (pr1 X) x.

  Definition monoidal_assoc
             (x y z : monoidal_carrier)
    : monoidal_mult x (monoidal_mult y z)
      =
      monoidal_mult (monoidal_mult x y) z
    := monoidal_PA_assoc (pr1 X) x y z.

  Definition monoidal_triangle
             (x y : monoidal_carrier)
    : maponpaths
        (λ z, monoidal_mult x z)
        (monoidal_lunit y)
      =
      (monoidal_assoc _ _ _)
      @ maponpaths
          (λ z, monoidal_mult z y)
          (monoidal_runit x).
  Proof.
    refine (_ @ pr2 X triangle (x ,, y) (idpath tt) @ _).
    - apply monoidal_triangle_left.
    - apply monoidal_triangle_right.
  Qed.

  Definition monoidal_pentagon
             (w x y z : monoidal_carrier)
    : monoidal_assoc w x (monoidal_mult y z)
      @ monoidal_assoc (monoidal_mult w x) y z
      =
      maponpaths
        (λ q, monoidal_mult w q)
        (monoidal_assoc x y z)
      @ monoidal_assoc w (monoidal_mult x y) z
      @ maponpaths
          (λ q, monoidal_mult q z)
          (monoidal_assoc w x y).
  Proof.
    refine (_ @ pr2 X pentagon (((w ,, x) ,, y) ,, z) (idpath tt) @ _).
    - apply monoidal_pentagon_left.
    - apply monoidal_pentagon_right.
  Qed.
End MonoidalAlgebraProjections.

Section MonoidalAlgebraBuilder.
  Variable (A : one_type)
           (e : A)
           (m : A → A → A)
           (unitl_m : ∏ (x : A), m e x = x)
           (unitr_m : ∏ (x : A), m x e = x)
           (assoc_m : ∏ (x y z : A), m x (m y z) = m (m x y) z)
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

  Local Definition build_monoidal_prealgebra
    : hit_prealgebra_one_types monoidal_signature.
  Proof.
    use make_hit_prealgebra.
    - apply A.
    - apply one_type_isofhlevel.
    - simpl ; intro x.
      induction x as [ | x].
      + exact e.
      + exact (m (pr1 x) (pr2 x)).
  Defined.

  Local Definition build_monoidal_path_algebra
    : hit_path_algebra_one_types monoidal_signature.
  Proof.
    use make_hit_path_algebra.
    - exact build_monoidal_prealgebra.
    - intros j x.
      induction j.
      + (* left unit *)
        exact (unitl_m x).
      + (* right unit *)
        exact (unitr_m x).
      + (* assoc *)
        exact (assoc_m (pr11 x) (pr21 x) (pr2 x)).
  Defined.

  Local Definition build_monoidal_path_is_algebra
    : is_hit_algebra_one_types monoidal_signature build_monoidal_path_algebra.
  Proof.
    intros j x p.
    induction j ; cbn in x.
    - refine (_ @ triangle_m (pr1 x) (pr2 x) @ _).
      + refine (!_).
        exact (monoidal_triangle_left build_monoidal_path_algebra (pr1 x) (pr2 x)).
      + refine (!_).
        exact (monoidal_triangle_right build_monoidal_path_algebra (pr1 x) (pr2 x)).
    - refine (_ @ pentagon_m (pr111 x) (pr211 x) (pr21 x) (pr2 x) @ _).
      + refine (!_).
        exact (monoidal_pentagon_left
                 build_monoidal_path_algebra
                 (pr111 x) (pr211 x) (pr21 x) (pr2 x)).
      + refine (!_).
        exact (monoidal_pentagon_right
                 build_monoidal_path_algebra
                 (pr111 x) (pr211 x) (pr21 x) (pr2 x)).
  Qed.

  Definition build_monoidal_algebra
    : hit_algebra_one_types monoidal_signature.
  Proof.
    use make_algebra.
    - exact build_monoidal_path_algebra.
    - exact build_monoidal_path_is_algebra.
  Defined.
End MonoidalAlgebraBuilder.

Definition concatenate_assoc
           {A : UU}
           (x y z : list A)
  : concatenate
      x
      (concatenate y z)
    =
    concatenate
      (concatenate x y)
      z.
Proof.
  revert x.
  apply list_ind.
  - apply idpath.
  - exact (λ x xs IHxs, maponpaths (cons x) IHxs).
Defined.

Definition list_triangle
           {A : UU}
           (x y : list A)
  : idpath (concatenate x (concatenate nil y))
    =
    concatenate_assoc x nil y
    @ maponpaths (λ z : list A, concatenate z y) (concatenate_nil x).
Proof.
  revert x.
  apply list_ind.
  - apply idpath.
  - intros x xs IHxs ; simpl.
    refine (maponpaths (maponpaths (cons x)) IHxs @ _) ; simpl.
    refine (maponpathscomp0 (cons x) _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply (maponpathscomp (λ z, concatenate z y) (cons x)).
    }
    refine (!_).
    apply (maponpathscomp (cons x) (λ z, concatenate z y)).
Qed.

Definition list_pentagon
           {A : UU}
           (w x y z : list A)
  : concatenate_assoc w x (concatenate y z)
    @ concatenate_assoc (concatenate w x) y z
    =
    maponpaths (λ q, concatenate w q) (concatenate_assoc x y z)
    @ concatenate_assoc w (concatenate x y) z
    @ maponpaths (λ q, concatenate q z) (concatenate_assoc w x y).
Proof.
  revert w x.
  use list_ind ; simpl.
  - use list_ind.
    + apply idpath.
    + simpl ; intros x xs IHxs.
      refine (maponpaths (maponpaths (cons x)) (IHxs @ pathscomp0rid _) @ _).
      refine (_ @ !((pathscomp0rid _))).
      refine (_ @ !(maponpathscomp
                      (cons x)
                      (λ q, concatenate nil q)
                      (concatenate_assoc xs y z))).
      exact (maponpathscomp (concatenate nil) (cons x) _).
  - intros w ws IHws x.
    refine (!(maponpathscomp0
                (cons w)
                (concatenate_assoc ws x (concatenate y z))
                (concatenate_assoc (concatenate ws x) y z))
            @ _).
    refine (maponpaths (maponpaths (cons w)) (IHws x) @ _).
    refine (maponpathscomp0 (cons w) _ _ @ _).
    refine (maponpaths (λ q, q @ _) (maponpathscomp (concatenate ws) (cons w) _) @ _).
    apply maponpaths.
    refine (maponpathscomp0 (cons w) _ _ @ _).
    apply maponpaths.
    refine (maponpathscomp (λ q, concatenate q z) (cons w) _ @ _).
    exact (!(maponpathscomp
               (cons w)
               (λ q, concatenate q z)
               (concatenate_assoc ws x y))).
Qed.

Definition list_monoidal_algebra
           (A : one_type)
  : hit_algebra_one_types monoidal_signature.
Proof.
  use build_monoidal_algebra.
  - refine (make_one_type (list A) _).
    apply isofhlevellist.
    apply one_type_isofhlevel.
  - exact nil.
  - exact concatenate.
  - exact nil_concatenate.
  - exact concatenate_nil.
  - exact concatenate_assoc.
  - exact list_triangle.
  - exact list_pentagon.
Defined.
