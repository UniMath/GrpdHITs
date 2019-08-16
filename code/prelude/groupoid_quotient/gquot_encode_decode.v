Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import prelude.basics.
Require Import prelude.cubical_methods.
Require Import groupoid_quotient.gquot.
Require Import groupoid_quotient.gquot_principles.

Local Open Scope cat.

(** * Encode-decode method for characterizing the path space of [gquot G]. *)
Section encode_decode.
  Variable (G : groupoid).

  (** First, we shall lift the hom set of [G] to a set relation of [gquot G].
      For that, we need an equivalence between [hom G a₁ b] and [hom G a₂ b] (given a morphism [hom G a₁ a₂]),
      and another one between [hom G a b₁] and [hom G a b₂] (given a morphism [hom G b₁ b₂]).
      Those are the [left_action] and the [right_action], resp.
   *)
  Definition right_action
        {a₁ a₂ : G} (b : G)
        (g : a₁ --> a₂)
    : a₁ --> b → a₂ --> b
    := λ h, inv_from_iso (g ,, pr2 G _ _ g) · h.

  Definition right_action_inv
             {a₁ a₂ : G} (b : G)
             (g : a₁ --> a₂)
    : a₂ --> b → a₁ --> b
    := λ h, g · h.

  Definition right_action_isweq
             (a : G) {b₁ b₂ : G}
             (g : b₁ --> b₂)
    : isweq (right_action a g).
  Proof.
    use gradth.
    - exact (right_action_inv a g).
    - abstract
        (intros h ; cbn ;
         unfold right_action, right_action_inv ; cbn ;
         rewrite !assoc ;
         rewrite (iso_inv_after_iso (g ,, _)) ;
         apply id_left).
    - abstract
        (intros h ; cbn ;
         unfold right_action, right_action_inv ; cbn ;
         rewrite !assoc ;
         rewrite (iso_after_iso_inv (g ,, _)) ;
         apply id_left).
  Defined.

  Definition left_action
        (a : G) {b₁ b₂ : G}
        (g : b₁ --> b₂)
    : a --> b₁ → a --> b₂
    := λ h, h · g.

  Definition left_action_inv
             (a : G) {b₁ b₂ : G}
             (g : b₁ --> b₂)
    : a --> b₂ → a --> b₁
    := λ h, h · (inv_from_iso (g ,, pr2 G _ _ g)).

  Definition left_action_isweq
             (a : G) {b₁ b₂ : G}
             (g : b₁ --> b₂)
    : isweq (left_action a g).
  Proof.
    use gradth.
    - exact (left_action_inv a g).
    - abstract
        (intros h ; cbn ;
         unfold left_action, left_action_inv ; cbn ;
         rewrite <- assoc ;
         rewrite (iso_inv_after_iso (g ,, _)) ;
         apply id_right).
    - abstract
        (intros h ; cbn ;
         unfold left_action, left_action_inv ; cbn ;
         rewrite <- assoc ;
         rewrite (iso_after_iso_inv (g ,, _)) ;
         apply id_right).
  Defined.

  (** The action of the unit element is the identity. *)
  Definition left_action_e (a b : G) (g : a --> b)
    : left_action a (identity b) g = g.
  Proof.
    apply id_right.
  Defined.

  Definition right_action_e (a b : G) (g : a --> b)
    : right_action b (identity a) g = g.
  Proof.
    unfold right_action.
    refine (_ @ id_left g).
    apply maponpaths_2.
    refine (!_).
    use inv_iso_unique'.
    unfold precomp_with ; cbn.
    apply id_left.
  Qed.

  Definition right_action_comp
             (a₁ a₂ a₃ b : G)
             (g₁ : a₁ --> a₂)
             (g₂ : a₂ --> a₃)
             (h : a₁ --> b)
    : right_action b (g₁ · g₂) h = right_action b g₂ (right_action b g₁ h).
  Proof.
    unfold right_action.
    rewrite assoc.
    apply maponpaths_2.
    refine (!_).
    use inv_iso_unique'.
    unfold precomp_with ; cbn.
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- !assoc.
      rewrite (iso_inv_after_iso (g₂ ,, _)).
      apply id_right.
    }
    rewrite (iso_inv_after_iso (g₁ ,, _)).
    apply idpath.
  Qed.

  (** The lift of [hom G] to [gquot G]. *)
  Definition g_fam : gquot G → gquot G → hSet.
  Proof.
    simple refine (gquot_relation G G
                          (λ (z₁ z₂ : G), make_hSet (z₁ --> z₂) _) 
                          (λ _ _ b g, right_action b g)
                          (λ a _ _ g, left_action a g)
                          _ _ _ _ _ _ _
                  ).
    - apply homset_property.
    - intros.
      apply right_action_isweq.
    - intros.
      apply left_action_isweq.
    - intros ? ? ? ; simpl.
      apply right_action_e.
    - intros ; intro ; cbn.
      apply right_action_comp.
    - intros a b g.
      apply left_action_e.
    - intros a b₁ b₂ b₃ g₁ g₂ h ; simpl.
      apply assoc.
    - intros a₁ a₂ b₁ b₂ g₁ g₂ h ; simpl.
      apply assoc.
  Defined.

  (** The computation rules of [g_fam] for the paths. *)
  Definition gquot_fam_l_gcleq
             {a₁ a₂ : G} (b : G) (g : a₁ --> a₂)
    : maponpaths (λ z, g_fam z (gcl G b)) (gcleq G g)
      =
      _
    := gquot_relation_beta_l_gcleq
         G G
         (λ (z₁ z₂ : G), make_hSet (z₁ --> z₂) _) 
         _ _ _ _ _ _ _ _ _ _ g.

  Definition gquot_fam_r_gcleq
             (a : G) {b₁ b₂ : G} (g : b₁ --> b₂)
    : maponpaths (g_fam (gcl G a)) (gcleq G g)
      =
      _
    := gquot_relation_beta_r_gcleq
         G G
         (λ (z₁ z₂ : G), make_hSet (z₁ --> z₂) _) 
         _ _ _ _ _ _ _ _ _ _ g.

  Opaque g_fam.

  (** The relation [g_fam] is reflexive. *)
  Definition g_fam_refl : ∏ (x : gquot G), g_fam x x.
  Proof.
    simple refine (gquot_ind_set (λ x, g_fam x x) _ _ _).
    - exact (λ a, identity a).
    - intros a₁ a₂ g.
      apply path_to_PathOver.
      refine ((transport_idmap_ap_set (λ x, g_fam x x) (gcleq G g) (identity a₁))
                @ _).
      refine (maponpaths (λ z, transportf _ z _) (_ @ _ @ _) @ _).
      + exact (ap_diag2 g_fam (gcleq G g)).
      + refine (maponpaths (λ z, z @ _) (gquot_fam_r_gcleq a₁ g) @ _).
        exact (maponpaths (λ z, _ @ z) (gquot_fam_l_gcleq a₂ g)).
      + exact (!(@path_HLevel_comp 2 _ _ _ _ _)).
      + refine (transport_path_hset _ _ @ _) ; simpl.
        unfold right_action, left_action ; simpl.
        refine (maponpaths (λ z, _ · z) (id_left _) @ _).
        exact (iso_after_iso_inv (g ,, _)).
    - intro.
      apply g_fam.
  Defined.

  (** Now we can define the encode function. *)
  Definition encode_gquot (x y : gquot G)
    : x = y → g_fam x y
    := λ p, transportf (g_fam x) p (g_fam_refl x).

  (** We can also define the decode function.
      For this we use double induction over a family of sets.
   *)
  Definition decode_gquot (x y : gquot G) : g_fam x y → x = y.
  Proof.
    simple refine (gquot_double_ind_set (λ x y, g_fam x y → x = y) _ _ x y).
    - intros a b.
      use funspace_isaset.
      exact (gtrunc G a b).
    - exact (λ _ _ g, gcleq G g).
    - intros ; simpl.
      simple refine (PathOver_arrow _ _ _ _ _ _) ; simpl.
      intro z.
      apply map_PathOver.
      refine (whisker_square
                (idpath _)
                (!(maponpaths_for_constant_function _ _))
                (!(maponpathsidfun _))
                _
                (maponpaths
                   (gcleq G)
                   ((!(id_right _))
                      @ maponpaths
                      (λ p, z · p)
                      (!(iso_after_iso_inv (g ,, pr2 G _ _ g)))
                      @ assoc _ _ _)
                   @ gconcat _ _ _)
             ).
      apply maponpaths.
      refine (_ @ !(transport_idmap_ap_set (g_fam (gcl G a)) (!(gcleq G g)) z)).
      refine (!(@transport_path_hset
                  (make_hSet (a --> b₂) _)
                  (make_hSet (a --> b₁) _)
                  (invweq (make_weq (left_action a g) (left_action_isweq a g))) z)
               @ _).
      refine (maponpaths (λ p, transportf _ p z) _).
      rewrite maponpathsinv0.
      refine (_ @ maponpaths (λ z, ! z) (!(gquot_fam_r_gcleq _ _))).
      apply (@path_HLevel_inv 2).
    - intros ; simpl.
      simple refine (PathOver_arrow _ _ _ _ _ _).
      intro z ; simpl.
      apply map_PathOver.
      refine (whisker_square
                (idpath _)
                (!(maponpathsidfun _))
                (!(maponpaths_for_constant_function _ _))
                _
                (!(gconcat _ _ _) @ !(pathscomp0rid _))
             ).
      apply maponpaths.
      refine (_ @ !(transport_idmap_ap_set (λ z, g_fam z (gcl G b)) (!(gcleq G g)) z)).
      refine (!(@transport_path_hset
                  (make_hSet (a₂ --> b) _)
                  (make_hSet (a₁ --> b) _)
                  (invweq (make_weq (right_action b g) (right_action_isweq b g))) z)
               @ _).
      refine (maponpaths (λ p, transportf pr1hSet p z) _).
      rewrite maponpathsinv0.
      refine (_ @ maponpaths (λ z, !z) (!(gquot_fam_l_gcleq b g))).
      apply (@path_HLevel_inv 2).
  Defined.

  (** The encode and decode maps are inverses of each other. *)
  Definition decode_gquot_encode_gquot
             {x y : gquot G}
             (p : x = y)
    : decode_gquot x y (encode_gquot x y p) = p.
  Proof.
    induction p.
    revert x.
    simple refine (gquot_ind_prop _ _ _).
    - intros a ; simpl.
      exact (ge _ _).
    - intro.
      exact (gtrunc G _ _ _ _).
  Defined.
  
  Definition encode_gquot_decode_gquot
    : ∏ {x y : gquot G} (p : g_fam x y), encode_gquot x y (decode_gquot x y p) = p.
  Proof.
    simple refine (gquot_double_ind_prop _ _ _).
    - simpl.
      intros a b.
      use impred ; intro.
      exact (setproperty (g_fam _ _) _ _).
    - intros a b g.
      unfold encode_gquot, g_fam_refl.
      simpl.
      refine (transport_idmap_ap_set
                (λ x : gquot G, g_fam (gcl G a) x)
                (gcleq G g)
                (identity a) @ _).
      refine (_ @ id_left g).
      rewrite gquot_fam_r_gcleq.
      rewrite transport_path_hset.
      apply idpath.
  Defined.

  Definition encode_gquot_isweq
    : ∏ {x y : gquot G}, isweq (encode_gquot x y).
  Proof.
    intros x y.
    use gradth.
    - exact (decode_gquot x y).
    - intros z.
      apply decode_gquot_encode_gquot.
    - intros z.
      apply encode_gquot_decode_gquot.
  Defined.
End encode_decode.
