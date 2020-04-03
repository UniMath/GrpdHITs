(**
Here we define the signature for the coequifier.
We also show that the HIT on that signature is indeed the coequifier.

Suppose that we have:
- 1-types `A` and `B`
- functions `f, g : A → B`
- homotopies `p, q : f ==> g`
Then we define the coequifier to be the following HIT:

HIT coequifier(p, q) :=
| inc : B → coequifier(p, q)
| homot : ∏ (a : A), ap inc (p a) = ap inc (q a)

This HIT satisfies the desired universal property. See
https://ncatlab.org/nlab/show/equifier
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.globe_over_lem.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra_map.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

Definition globe_PathOver_inConstantFamily
           {A B : one_type}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           (g : p₁ = p₂)
           {b₁ b₂ : B}
           {q₁ q₂ : b₁ = b₂}
           (h : q₁ = q₂)
  : globe_over
      (λ (x : A), B)
      g
      (PathOver_inConstantFamily p₁ q₁)
      (PathOver_inConstantFamily p₂ q₂).
Proof.
  induction g, p₁.
  exact h.
Qed.

Definition apd_2_1
           {A B : UU}
           {Y : B → UU}
           {c : A → B}
           (cc : ∏ (a : A), Y (c a))
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : PathOver (cc a₁) (cc a₂) (maponpaths c p).
Proof.
  induction p ; apply idpath.
Defined.

Definition apd_2_first
           {A B : UU}
           {Y₁ : A → UU}
           {Y₂ : B → UU}
           {c : A → B}
           (cc : ∏ (a : A), Y₂ (c a))
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {y₁ : Y₁ a₁} {y₂ : Y₁ a₂}
           (q : PathOver y₁ y₂ p)
  : globe_over
      Y₂
      (idpath _)
      (apd_2 (λ z _, cc z) p q)
      (apd_2_1 cc p).
Proof.
  induction p, q.
  apply idpath.
Qed.

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

Definition sem_fmap_funextsec_eq
           {A : poly_code}
           {X Y : one_type}
           {f g : X → Y}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {TR : poly_code}
           {al ar : endpoint A (C X) TR}
           (p : f ~ g)
           {Z : UU}
           {c : poly_act A Z → Z}
           (q : ∏ i : J, homotsec (sem_endpoint_UU (l i) c) (sem_endpoint_UU (r i) c))
           {z : poly_act (C X) Z}
           (p_arg : sem_endpoint_UU al c z = sem_endpoint_UU ar c z)       
  : sem_homot_endpoint_UU (fmap_eq (funextsec _ _ _ p)) Z c q z p_arg = p z.
Proof.
  refine (sem_fmap_eq _ _ _ _ _ _ @ _).
  exact (eqtohomot (toforallpaths_funextsec p) z).
Qed.

Definition homot_endpoint_dact_fmap_eq
           {A : poly_code}
           {B₁ B₂ : one_type}
           {f g : B₁ → B₂}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {X : total_bicat
                  (disp_depprod_bicat
                     J
                     (λ j, add_cell_disp_cat
                             _ _ _
                             (sem_endpoint_one_types (l j))
                             (sem_endpoint_one_types (r j))))}
           {Y : pr111 X → one_type}
           (cX : ∏ (x : poly_act A (pr111 X)),
                 poly_dact_UU A Y x
                 →
                 Y ((pr21 X) x))
           (pX : ∏ (j : J)
                   (x : poly_act (S j) (pr111 X))
                   (y : poly_dact_UU (S j) Y x),
                 @PathOver
                   _
                   (sem_endpoint_UU (l j) (pr21 X) x)
                   _ _
                   (endpoint_dact (pr1 X) Y (l j) cX y)
                   (endpoint_dact (pr1 X) Y (r j) cX y)
                   (pr2 X j x))
           {TR : poly_code}
           {al ar : endpoint A (C B₁) TR}
           {b₁ b₂ : B₁}
           {p_arg : sem_endpoint_UU al (pr21 X) b₁ = sem_endpoint_UU ar (pr21 X) b₁}
           (pp_arg : @PathOver
                       _
                       (sem_endpoint_UU al _ _)
                       _ _
                       (endpoint_dact (pr1 X) Y al cX b₂)
                       (endpoint_dact (pr1 X) Y ar cX b₂)
                       p_arg)
           (p : f = g)
  : globe_over
      (λ _, B₂)
      (idpath _)
      (homot_endpoint_dact (fmap_eq p) cX pX _ pp_arg)
      (PathOver_inConstantFamily _ (toforallpaths _ _ _ p b₂)).
Proof.
  induction p.
  apply idpath.
Qed.

Definition homot_endpoint_dact_funext_fmap_eq
           {A : poly_code}
           {B₁ B₂ : one_type}
           {f g : B₁ → B₂}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {X : total_bicat
                  (disp_depprod_bicat
                     J
                     (λ j, add_cell_disp_cat
                             _ _ _
                             (sem_endpoint_one_types (l j))
                             (sem_endpoint_one_types (r j))))}
           {Y : pr111 X → one_type}
           (cX : ∏ (x : poly_act A (pr111 X)),
                 poly_dact_UU A Y x
                 →
                 Y ((pr21 X) x))
           (pX : ∏ (j : J)
                   (x : poly_act (S j) (pr111 X))
                   (y : poly_dact_UU (S j) Y x),
                 @PathOver
                   _
                   (sem_endpoint_UU (l j) (pr21 X) x)
                   _ _
                   (endpoint_dact (pr1 X) Y (l j) cX y)
                   (endpoint_dact (pr1 X) Y (r j) cX y)
                   (pr2 X j x))
           {TR : poly_code}
           {al ar : endpoint A (C B₁) TR}
           {b₁ b₂ : B₁}
           {p_arg : sem_endpoint_UU al (pr21 X) b₁ = sem_endpoint_UU ar (pr21 X) b₁}
           (pp_arg : @PathOver
                       _
                       (sem_endpoint_UU al _ _)
                       _ _
                       (endpoint_dact (pr1 X) Y al cX b₂)
                       (endpoint_dact (pr1 X) Y ar cX b₂)
                       p_arg)
           (p : f ~ g)
  : globe_over
      (λ _, B₂)
      (sem_fmap_funextsec_eq p (pr2 X) p_arg)
      (homot_endpoint_dact (fmap_eq (funextsec _ _ _ p)) cX pX _ pp_arg)
      (PathOver_inConstantFamily _ (p b₂)).
Proof.
  refine (concat_globe_over
            (homot_endpoint_dact_fmap_eq _ _ _ _)
            _).
  use globe_PathOver_inConstantFamily.
  exact (eqtohomot (toforallpaths_funextsec p) b₂).
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
    apply ap_e.
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
    apply ap_e.
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
    - exact (λ _, C A).
    - exact (λ _, C unit_one_type).
    - exact (λ _, c (C A) (tt : unit_one_type)).
    - exact (λ _, c (C A) (tt : unit_one_type)).
    - intro. exact s_endpoint.
    - intro. exact t_endpoint.
    - intro. exact left_homot_endpoint.
    - intro. exact right_homot_endpoint.
  Defined.

  (** Projections and builders *)
  Section CoequifierProjections.
    Context (X : hit_algebra_one_types coequifier_signature).

    Definition coequif_inc
      : B → alg_carrier X
      := alg_constr X.

    Definition coequif_homot
               (x : A)
      : maponpaths coequif_inc (p x)
        =
        maponpaths coequif_inc (q x).
    Proof.
      exact (maponpaths (maponpaths coequif_inc) (!(sem_fmap_funextsec_eq _ _ _))
             @ alg_homot X tt x (idpath _)
             @ maponpaths (maponpaths coequif_inc) ((sem_fmap_funextsec_eq _ _ _))).
    Qed.
  End CoequifierProjections.

  Section MakeCoequifierAlgebra.
    Context {X : one_type}
            (inc : B → X)
            (homot : ∏ (x : A),
                     maponpaths inc (p x)
                     =
                     maponpaths inc (q x)).

    Local Definition make_coequifier_path_algebra
      : hit_path_algebra_one_types coequifier_signature.
    Proof.
      use make_hit_path_algebra.
      - use make_hit_prealgebra.
        + exact X.
        + apply one_type_isofhlevel.
        + exact inc.
      - intro j ; induction j.
    Defined.

    Local Definition make_coequifier_is_algebra
      : is_hit_algebra_one_types coequifier_signature make_coequifier_path_algebra.
    Proof.
      intros j x r ; simpl in x.
      exact (maponpaths (maponpaths inc) (sem_fmap_funextsec_eq _ _ _)
             @ homot x
             @ maponpaths (maponpaths inc) (!(sem_fmap_funextsec_eq _ _ _))).
    Qed.
    
    Definition make_coequifier_algebra
      : hit_algebra_one_types coequifier_signature.
    Proof.
      use make_algebra.
      - exact make_coequifier_path_algebra.
      - exact make_coequifier_is_algebra.
    Defined.
  End MakeCoequifierAlgebra.

  Section CoequifierMapProjections.
    Context {X Y : hit_algebra_one_types coequifier_signature}
            (φ : X --> Y).

    Definition coequifier_map
      : alg_carrier X → alg_carrier Y
      := pr111 φ.

    Definition coequifier_map_inc
               (b : B)
      : coequifier_map (coequif_inc X b) = coequif_inc Y b
      := pr1 (pr211 φ) b.
  End CoequifierMapProjections.

  Section MakeCoequifierMap.
    Context {X Y : hit_algebra_one_types coequifier_signature}
            (φ : alg_carrier X → alg_carrier Y)
            (φ_inc : ∏ (b : B), φ (coequif_inc X b) = coequif_inc Y b).

    Definition make_coequifier_map
      : X --> Y.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - use make_hit_prealgebra_mor.
        + exact φ.
        + exact φ_inc.
      - intro i ; induction i.
    Defined.
  End MakeCoequifierMap.

  Section CoequifierCellProjections.
    Context {X Y : hit_algebra_one_types coequifier_signature}
            {φ ψ : X --> Y}
            (α : φ ==> ψ).

    Definition coequifier_cell
      : coequifier_map φ ~ coequifier_map ψ
      := pr111 α.

    Definition coequifier_cell_inc
               (b : B)
      : coequifier_cell (coequif_inc X b) @ coequifier_map_inc ψ b
        =
        coequifier_map_inc φ b.
    Proof.
      exact (eqtohomot (pr211 α) _ @ pathscomp0rid _).
    Qed.
  End CoequifierCellProjections.

  Section MakeCoequifierCell.
    Context {X Y : hit_algebra_one_types coequifier_signature}
            {φ ψ : X --> Y}
            (α : coequifier_map φ ~ coequifier_map ψ)
            (α_inc : ∏ (b : B),
                     α (coequif_inc X b) @ coequifier_map_inc ψ b
                     =
                     coequifier_map_inc φ b).

    Definition make_coequifier_cell
      : φ ==> ψ.
    Proof.
      simple refine (((α ,, _) ,, (λ _, tt)) ,, tt).
      abstract
        (use funextsec ; intro b ;
         exact (α_inc _ @ !(pathscomp0rid _))).
    Defined.
  End MakeCoequifierCell.

  (** The induction principle *)
  Section CoequifierInduction.
    Context {X : hit_algebra_one_types coequifier_signature}
            (Y : alg_carrier X → one_type)
            (Yinc : ∏ (b : B), Y (coequif_inc _ b))
            (Yhomot : ∏ (x : A),
                      globe_over
                        Y
                        (coequif_homot _ x)
                        (apd_depfun
                           (λ z, B)
                           Y
                           (λ b _, Yinc b)
                           (PathOver_inConstantFamily _ (p x)))
                        (apd_depfun
                           (λ z, B)
                           Y
                           (λ b _, Yinc b)
                           (PathOver_inConstantFamily _ (q x)))).

    Definition make_coequifier_disp_alg
      : disp_algebra X.
    Proof.
      use make_disp_algebra.
      - exact Y.
      - simpl ; intros b bb.
        exact (Yinc b).
      - intro j.
        induction j.
      - simpl ; intros j z zz r rr.
        refine (globe_over_move_globe_one_type
                  (one_type_isofhlevel (pr111 X))
                  (concat_globe_over
                     _
                     (concat_globe_over
                        (Yhomot z)
                        _))).
        + refine (concat_globe_over
                    _
                    _).
          * use apd2_globe_over.
            ** exact (p z).
            ** apply sem_fmap_funextsec_eq.
            ** unfold dep_constfun_fun in *.
               apply PathOver_inConstantFamily.
               exact (p zz).
            ** apply homot_endpoint_dact_funext_fmap_eq.
          * refine (concat_globe_over
                      (apd_2_first _ _)
                      _).
            exact (inv_globe_over (apd_2_first _ _)).
        + refine (inv_globe_over _).
          refine (concat_globe_over
                    _
                    _).
          * use apd2_globe_over.
            ** exact (q z).
            ** apply sem_fmap_funextsec_eq.
            ** unfold dep_constfun_fun in *.
               apply PathOver_inConstantFamily.
               exact (q zz).
            ** apply homot_endpoint_dact_funext_fmap_eq.
          * refine (concat_globe_over
                      (apd_2_first _ _)
                      _).
            exact (inv_globe_over (apd_2_first _ _)).
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
      : coequif_ind (coequif_inc _ b) = Yinc b
      := pr12 coequif_ind_disp_algebra_map b.
  End CoequifierInduction.

  (** Initiality of coequifier *)
  Definition coequifier_one_types_algebra
    : hit_algebra_one_types coequifier_signature
    := pr1 (hit_existence coequifier_signature).

  Definition coequifier_one_types_is_initial
    : is_initial _ coequifier_one_types_algebra.
  Proof.
    apply HIT_is_initial.
    exact (pr2 (hit_existence coequifier_signature)).
  Defined.

  Definition coequifier_one_types
    : one_types
    := hit_carrier coequifier_signature.

  Definition coequifier_one_types_inc
    : one_types ⟦ B , coequifier_one_types ⟧
    := coequif_inc coequifier_one_types_algebra.

  Definition coequifier_one_types_homot
    : p ▹ coequifier_one_types_inc = q ▹ coequifier_one_types_inc.
  Proof.
    use funextsec.
    exact (λ x, coequif_homot coequifier_one_types_algebra x).
  Qed.

  Section CoequfierUMPMap.
    Variable (Y : one_types)
             (Yinc : one_types ⟦ B , Y ⟧)
             (Yhomot : p ▹ Yinc = q ▹ Yinc).

    Local Definition coequifier_ump_1_Y_alg
      : hit_algebra_one_types coequifier_signature.
    Proof.
      exact (make_coequifier_algebra Yinc (λ x, eqtohomot Yhomot x)).
    Defined.

    Local Definition coequifier_ump_1_alg_map
      : coequifier_one_types_algebra
        -->
        coequifier_ump_1_Y_alg.
    Proof.
      exact (biinitial_1cell
               _
               coequifier_one_types_is_initial
               coequifier_ump_1_Y_alg).
    Defined.

    Definition coequifier_ump_1
      : coequifier_one_types --> Y
      := coequifier_map coequifier_ump_1_alg_map.

    Definition coequifier_ump_1_inc
      : coequifier_one_types_inc · coequifier_ump_1
        ==>
        Yinc
      := coequifier_map_inc coequifier_ump_1_alg_map.
  End CoequfierUMPMap.

  Section CoequifierUMPCell.
    Context {Y : one_types}
            {Yinc : one_types ⟦ B , Y ⟧}
            {Yhomot : p ▹ Yinc = q ▹ Yinc}
            (φ ψ : coequifier_one_types --> Y)
            (φinc : coequifier_one_types_inc · φ ==> Yinc)
            (ψinc : coequifier_one_types_inc · ψ ==> Yinc).
    
    Local Definition coequifier_ump_2_alg_cell
      : @make_coequifier_map
          coequifier_one_types_algebra
          (make_coequifier_algebra Yinc (λ x, eqtohomot Yhomot x))
          φ
          φinc
        ==>
        @make_coequifier_map
           coequifier_one_types_algebra
           (make_coequifier_algebra Yinc (λ x, eqtohomot Yhomot x))
           ψ
           ψinc
      := biinitial_2cell
           _
           coequifier_one_types_is_initial
           _ _.

    Definition coequifier_ump_2
      : φ ==> ψ
      := coequifier_cell coequifier_ump_2_alg_cell.

    Definition coequifier_ump_2_inc
      : (coequifier_one_types_inc ◃ coequifier_ump_2) • ψinc
        =
        φinc.
    Proof.
      use funextsec ; intro b.
      exact (coequifier_cell_inc coequifier_ump_2_alg_cell b).
    Qed.
  End CoequifierUMPCell.

  Section CoequifierUMPEq.
    Context {Y : one_types}
            {Yinc : one_types ⟦ B , Y ⟧}
            {Yhomot : p ▹ Yinc = q ▹ Yinc}
            {φ ψ : coequifier_one_types --> Y}
            {φinc : coequifier_one_types_inc · φ ==> Yinc}
            {ψinc : coequifier_one_types_inc · ψ ==> Yinc}
            (ρ σ : φ ==> ψ)
            (ρinc : (coequifier_one_types_inc ◃ ρ) • ψinc = φinc)
            (σinc : (coequifier_one_types_inc ◃ σ) • ψinc = φinc).

    Definition coequifier_ump_eq
      : ρ = σ.
    Proof.
      pose
        (@biinitial_eq
           _ _
           _ coequifier_one_types_is_initial
           _
           _ _
           (@make_coequifier_cell
              _ _
              (@make_coequifier_map
                 coequifier_one_types_algebra
                 (make_coequifier_algebra Yinc (λ x, eqtohomot Yhomot x))
                 φ
                 φinc)
              (@make_coequifier_map
                 coequifier_one_types_algebra
                 (make_coequifier_algebra Yinc (λ x, eqtohomot Yhomot x))
                 ψ
                 ψinc)
              ρ (eqtohomot ρinc))
           (@make_coequifier_cell
              _ _
              (@make_coequifier_map
                 coequifier_one_types_algebra
                 (make_coequifier_algebra Yinc (λ x, eqtohomot Yhomot x))
                 φ
                 φinc)
              (@make_coequifier_map
                 coequifier_one_types_algebra
                 (make_coequifier_algebra Yinc (λ x, eqtohomot Yhomot x))
                 ψ
                 ψinc)
              σ (eqtohomot σinc)))
        as w.
      exact (maponpaths (λ z, pr111 z) w).
    Qed.
  End CoequifierUMPEq.
End CoequifierSignature.
    
