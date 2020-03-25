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
Require Import displayed_algebras.globe_over_lem.
Require Import displayed_algebras.displayed_algebra.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Definition fmap_eq
           {A : poly_code}
           {X Y : one_type}
           {f g : X → Y}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {TR : poly_code}
           {al ar : endpoint A (C X) TR}
           (p : f = g)
  : homot_endpoint
      l r
      al ar
      (fmap f)
      (fmap g).
Proof.
  induction p.
  apply refl_e.
Defined.

Definition sem_fmap_eq
           {A : poly_code}
           {X Y : one_type}
           {f g : X → Y}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {TR : poly_code}
           {al ar : endpoint A (C X) TR}
           (p : f = g)
           (x : X)
           (Z : UU)
           (c : poly_act A Z → Z)
           (q : ∏ i : J, homotsec (sem_endpoint_UU (l i) c) (sem_endpoint_UU (r i) c))
           (z : poly_act (C X) Z)
           (p_arg : sem_endpoint_UU al c z = sem_endpoint_UU ar c z)       
  : sem_homot_endpoint_UU (fmap_eq p) Z c q z p_arg = toforallpaths _ f g p z.
Proof.
  induction p.  
  apply idpath.
Qed.
                                            
Section CoequifierSignature.
  Context
    (A B : one_type)
    (f g : A → B)
    (p q : ∏ (x : A), f x = g x).
  
  Definition no_endpoint
    : ∏ j : ∅, endpoint (C B) (fromempty j) I.
  Proof.
    intro j. induction j.
  Qed.

  (** i (f x) **)
  Definition s_endpoint
    : endpoint (C B) (C A) I
    := comp (fmap f) constr.

  (** i (g x) **)
  Definition t_endpoint
    : endpoint (C B) (C A) I
    := comp (fmap g) constr.

  Definition left_homot_endpoint
    : homot_endpoint
        no_endpoint
        no_endpoint
        (c (C A) (tt : unit_one_type))
        (c (C A) (tt : unit_one_type))
        s_endpoint
        t_endpoint.
  Proof.
    simpl.
    unfold s_endpoint.
    unfold t_endpoint.
    apply ap_constr.
    apply fmap_eq.
    apply funextsec.
    exact p.
  Defined.

  Definition right_homot_endpoint
    : homot_endpoint
        no_endpoint
        no_endpoint
        (c (C A) (tt : unit_one_type))
        (c (C A) (tt : unit_one_type))
        s_endpoint
        t_endpoint.
  Proof.
    simpl.
    unfold s_endpoint.
    unfold t_endpoint.
    apply ap_constr.
    apply fmap_eq.
    apply funextsec.
    exact q.
  Defined.

  Definition coequifier_signature
    : hit_signature.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
    - exact (C B).
    - exact empty.
    - exact fromempty.
    - exact no_endpoint.
    - exact no_endpoint.
    - exact unit.
    - intro. exact (C A).
    - intro. exact (C unit_one_type).
    - intro. exact (c (C A) (tt : unit_one_type)).
    - intro. exact (c (C A) (tt : unit_one_type)).
    - intro. exact s_endpoint.
    - intro. exact t_endpoint.
    - intro. exact left_homot_endpoint.
    - intro. exact right_homot_endpoint.
  Defined.

  Section CoequifierProjections.
    Context {X : hit_algebra_one_types coequifier_signature}.

    Definition coequif_inc
      : B → alg_carrier X
      := alg_constr X.

    Definition coequif_homot
               (x : A)
      : maponpaths
          coequif_inc
          (p x)
        =
        maponpaths
          coequif_inc
          (q x).
    Proof.
      pose (alg_homot X tt x (idpath _)) as i.
      simpl in i.
      cbn in i.
      refine (_ @ i @ _).
      - apply maponpaths.
        apply TODO.
      - apply maponpaths.
        apply TODO.
    Defined.
  End CoequifierProjections.

  Section CoequifierInduction.
    Context {X : hit_algebra_one_types coequifier_signature}
            (Y : alg_carrier X → one_type)
            (Yinc : ∏ (b : B), Y (coequif_inc b))
            (Yhomot : ∏ (x : A),
                      globe_over
                        Y
                        (coequif_homot x)
                        (@apd_2
                           _ _ (λ z, Y(coequif_inc z)) _
                           coequif_inc (λ z _, Yinc z)
                           _ _ _ _ _
                           (apd Yinc (p x)))
                        (@apd_2
                           _ _ (λ z, Y(coequif_inc z)) _
                           coequif_inc (λ z _, Yinc z)
                           _ _ _ _ _
                           (apd Yinc (q x)))).
             
    Definition make_coequifier_disp_alg
      : disp_algebra X.
    Proof.
      use make_disp_algebra.
      - exact Y.
      - simpl ; intros b bb.
        exact (Yinc b).
      - intro j.
        induction j.
      - (*simpl ; intros j z zz r rr.
        cbn in z, zz.
        refine (globe_over_move_globe_one_type
                  _
                  (concat_globe_over
                     _
                     (concat_globe_over
                        (Yhomot z)
                        _))).
        { apply (one_type_isofhlevel (pr111 X)). }
        apply TODO.
        apply TODO.*)
        apply TODO.
    Defined.

    Variable (HX : is_HIT coequifier_signature X).

    (** Induction principle *)
    Definition coequif_ind_disp_algebra_map
      : disp_algebra_map make_coequifier_disp_alg
      := HX make_coequifier_disp_alg.

    Definition coequif_ind
      : ∏ (x : alg_carrier X), Y x
      := pr1 coequif_ind_disp_algebra_map.

    Definition coequif_ind_base
               (b : B)
      : coequif_ind (coequif_inc b) = Yinc b
      := pr12 coequif_ind_disp_algebra_map b.
  End CoequifierInduction.
End CoequifierSignature.
  

    
