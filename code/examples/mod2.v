(**
Here we define the signature for the integers modulo 2.

These are defined as the following HIT:
HIT mod2 :=
| 0 : mod2
| S : mod2 → mod2
| mod : ∏ (n : mod2), S(S n) = n
| ap_mod : ∏ (n : mod2), ap S (mod n) = mod (S n)
We study the 1-truncation.
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
Require Import displayed_algebras.globe_over_lem.

Local Open Scope cat.

Definition mod2_point_constr
  : poly_code
  := C unit_one_type + I.

Definition mod2_paths : UU := unit.

Definition mod2_paths_args (j : mod2_paths) : poly_code := I.

Definition zero_e
           (P : poly_code)
  : endpoint mod2_point_constr P I
  := comp
       (comp
          (c P (tt : unit_one_type))
          (ι₁ _ _))
       constr.


Definition suc_e
           {P : poly_code}
           (e : endpoint mod2_point_constr P I)
  : endpoint mod2_point_constr P I
  := comp e (comp (ι₂ _ _) constr).

Definition mod2_paths_lhs
           (i : mod2_paths)
  : endpoint mod2_point_constr (mod2_paths_args i) I
  := suc_e (suc_e (id_e _ _)).

Definition mod2_paths_rhs
           (i : mod2_paths)
  : endpoint mod2_point_constr (mod2_paths_args i) I
  := id_e _ _.

Definition mod2_homots : UU := unit.

Definition mod2_homots_point_arg
           (i : mod2_homots)
  : poly_code
  := I.

Definition mod2_homots_point_left_endpoint
           (i : mod2_homots)
  : endpoint mod2_point_constr (mod2_homots_point_arg i) I
  := suc_e (suc_e (suc_e (id_e _ _))).

Definition mod2_homots_point_right_endpoint
           (i : mod2_homots)
  : endpoint mod2_point_constr (mod2_homots_point_arg i) I
  := suc_e (id_e _ _).

Definition mod2_e
           {i : mod2_homots}
           (e : endpoint mod2_point_constr (mod2_homots_point_arg i) I)
  : homot_endpoint
      mod2_paths_lhs
      mod2_paths_rhs
      (c (mod2_homots_point_arg i) (tt : unit_one_type))
      (c (mod2_homots_point_arg i) (tt : unit_one_type))
      (suc_e (suc_e e))
      e
  := trans_e
       (ap_e
          _
          (trans_e
             (ap_e
                _
                (inv_e (comp_id_r _)))
             (inv_e (comp_assoc _ _ _))))
       (trans_e
          (inv_e (comp_assoc _ _ _))
          (trans_e
             (path_constr tt _)
             (comp_id_r _))).

Definition ap_suc_e
           {i : mod2_homots}
           {e₁ e₂ : endpoint mod2_point_constr (mod2_homots_point_arg i) I}
           (h : homot_endpoint
                  mod2_paths_lhs
                  mod2_paths_rhs
                  (c (mod2_homots_point_arg i) (tt : unit_one_type))
                  (c (mod2_homots_point_arg i) (tt : unit_one_type))
                  e₁
                  e₂)
  : homot_endpoint
      mod2_paths_lhs
      mod2_paths_rhs
      (c (mod2_homots_point_arg i) (tt : unit_one_type))
      (c (mod2_homots_point_arg i) (tt : unit_one_type))
      (suc_e e₁)
      (suc_e e₂)
  := trans_e
       (comp_assoc _ _ _)
       (trans_e
          (ap_e _ (ap_e _ h))
          (inv_e (comp_assoc _ _ _))).
  
Definition mod2_homots_point_rhs
           (i : mod2_homots)
  : homot_endpoint
      mod2_paths_lhs
      mod2_paths_rhs
      (c (mod2_homots_point_arg i) (tt : unit_one_type))
      (c (mod2_homots_point_arg i) (tt : unit_one_type))
      (mod2_homots_point_left_endpoint i)
      (mod2_homots_point_right_endpoint i)
  := ap_suc_e 
       (trans_e
          (inv_e (comp_id_l _))
          (trans_e
             (path_constr tt _)
             (comp_id_l _))).

Definition mod2_homots_point_lhs
           (i : mod2_homots)
  : homot_endpoint
      mod2_paths_lhs
      mod2_paths_rhs
      (c (mod2_homots_point_arg i) (tt : unit_one_type))
      (c (mod2_homots_point_arg i) (tt : unit_one_type))
      (suc_e (suc_e (suc_e (id_e _ _))))
      (suc_e (id_e _ _))
  := mod2_e (suc_e (id_e _ _)).
  
Definition mod2_signature
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact mod2_point_constr.
  - exact mod2_paths.
  - exact mod2_paths_args.
  - exact mod2_paths_lhs.
  - exact mod2_paths_rhs.
  - exact mod2_homots.
  - exact mod2_homots_point_arg.
  - exact (λ _, C unit_one_type).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact mod2_homots_point_left_endpoint.
  - exact mod2_homots_point_right_endpoint.
  - exact mod2_homots_point_lhs.
  - exact mod2_homots_point_rhs.
Defined.

Section Mod2AlgebraProjections.
  Variable (X : hit_algebra_one_types mod2_signature).

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
    := pr21 X tt.

  Definition mod2_ap_mod
    : ∏ (n : mod2_carrier),
      maponpaths mod2_S (mod2_mod n)
      =
      mod2_mod (mod2_S n).
  Proof.
    intro n.
    refine (!(maponpathscomp inr (pr211 X) (mod2_mod n)) @_).
    refine (_@ pathscomp0rid _).
    refine (_@ !(pr2 X tt n (idpath _))).
    refine (_@ !(pathscomp0rid _)).
    rewrite pathscomp0rid.
    apply idpath.
  Defined.
End Mod2AlgebraProjections.

Section Mod2Induction.
  Context {X : hit_algebra_one_types mod2_signature}
          (Y : alg_carrier X → one_type)
          (YZ : Y (mod2_Z X))
          (YS : ∏ (n : alg_carrier X), Y n → Y (mod2_S X n))
          (Ymod : ∏ (n : alg_carrier X) (y : Y n),
                  @PathOver _ _ _ (mod2_mod X n) Y (YS _ (YS n y)) y)
          (Yap_mod : ∏ (n : alg_carrier X)
                       (nn : Y n),
                     globe_over
                       Y
                       (mod2_ap_mod X n)
                       (@apd_2 _ _ _ Y (mod2_S X) YS _ _ (mod2_mod X n) _ _ (Ymod n nn))
                       (Ymod (mod2_S X n) (YS n nn))).

  Local Definition cY
    : ∏ (x : poly_act (point_constr mod2_signature) (alg_carrier X)),
      poly_dact (point_constr mod2_signature) Y x → Y (alg_constr X x).
  Proof.
    intros x xx.
    induction x as [ | x].
    - induction a.
      exact YZ.
    - exact (YS x xx).
  Defined.

  Definition make_mod2_disp_algebra
    : disp_algebra X.
  Proof.
    use make_disp_algebra.
    - exact Y.
    - exact cY.
    - intros j x y.
      induction j.
      exact (Ymod x y).
    - abstract
        (intros j n nn p pp ;
         induction j ;
         refine (globe_over_move_globe_one_type _ _) ;
         [ apply (pr111 X)
         | refine (concat_globe_over
                     (globe_over_compose_left'
                        _
                        (globe_over_id_left _))
                     _) ;
           refine (concat_globe_over
                     (globe_over_compose_left'
                        _
                        (globe_over_id_right _))
                     _) ;
           refine (inv_globe_over _) ;
           refine (concat_globe_over
                     (globe_over_id_left _)
                     _) ;
           refine (concat_globe_over
                     (globe_over_id_right _)
                     _) ;
           refine (concat_globe_over
                     (apd2_comp dep_inr_fun _ _)
                     _) ;
           refine (concat_globe_over
                     (@apd2_globe_over
                        _ _ Y Y
                        _ YS
                        _ _ _ _ _ _ _ _ _
                        (concat_globe_over
                           (globe_over_id_left _)
                           (globe_over_id_right _)))
                     _) ;
           refine (concat_globe_over
                     (Yap_mod n nn)
                     _) ;
           refine (inv_globe_over _) ;
           apply globe_over_id_left]).
  Defined.  

  Variable (HX : is_HIT mod2_signature X).

  (** Induction principle *)
  Definition mod2_ind_disp_algebra_map
    : disp_algebra_map make_mod2_disp_algebra
    := HX make_mod2_disp_algebra.

  Definition mod2_ind
    : ∏ (x : alg_carrier X), Y x
    := pr1 mod2_ind_disp_algebra_map.

  Definition mod2_ind_Z
    : mod2_ind (mod2_Z X) = YZ
    := pr12 mod2_ind_disp_algebra_map (inl tt).

  Definition mod2_ind_S
             (n : alg_carrier X)
    : mod2_ind (mod2_S X n) = YS n (mod2_ind n)
    := pr12 mod2_ind_disp_algebra_map (inr n).
  
  Definition mod2_ind_mod
             (n : alg_carrier X)
    : PathOver_square
        _
        (idpath _)
        (apd (pr1 mod2_ind_disp_algebra_map) (alg_path X tt n))
        (Ymod n (pr1 mod2_ind_disp_algebra_map n))
        (pr12 mod2_ind_disp_algebra_map
              (inr ((pr211 X) (inr n)))
         @ maponpaths
             (λ x : Y ((pr211 X) (inr n)), YS ((pr211 X) (inr n)) x)
             ((pr12 mod2_ind_disp_algebra_map) (inr n)))
        (idpath (pr1 mod2_ind_disp_algebra_map n)).
  Proof.
    pose (pr22 mod2_ind_disp_algebra_map tt n) as p.
    simpl in p.
    cbn in p.
    rewrite !pathscomp0rid in p.
    exact p.
  Qed.
End Mod2Induction.
