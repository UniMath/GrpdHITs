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

Local Open Scope cat.

Section gquot_rec.
  Variable (G : groupoid)
           (Y : UU)
           (gclY : G → Y)
           (gcleqY : ∏ {a₁ a₂ : G},
               a₁ --> a₂ → gclY a₁ = gclY a₂)
           (geY : ∏ (a : G), gcleqY (identity a) = idpath _)
           (gconcatY : ∏ (a₁ a₂ a₃: G) (g₁: a₁ --> a₂) (g₂: a₂ --> a₃),
               gcleqY (g₁ · g₂) = gcleqY g₁ @ gcleqY g₂)
           (truncY : isofhlevel 3 Y).

  Definition gquot_rec : gquot G → Y.
  Proof.
    simple refine (gquot_ind
                     (λ _, Y)
                     gclY
                     (λ a₁ a₂ g, PathOver_inConstantFamily _ (gcleqY g))
                     (λ a, const_globe_over
                                 (ge G a)
                                 (gcleqY (identity a))
                                 (idpath _)
                                 (geY a))
                     _
                     (λ _, truncY)) ; simpl.
    intros a₁ a₂ a₃ g₁ g₂.
    simple refine (globe_over_whisker
                     (λ _, Y)
                     _
                     (idpath _)
                     (PathOver_inConstantFamily_concat _ _)
                     (const_globe_over
                        (gconcat G g₁ g₂)
                        (gcleqY (g₁ · g₂))
                        (gcleqY g₁ @ gcleqY g₂)
                        (gconcatY a₁ a₂ a₃ g₁ g₂)
                     )
                  ).
  Defined.

  Definition gquot_rec_beta_gcleq (a₁ a₂ : G) (g : a₁ --> a₂)
    : maponpaths gquot_rec (gcleq G g) = gcleqY g.
  Proof.
    apply (PathOver_inConstantFamily_inj (gcleq G g)).
    refine (!(apd_const _ _) @ _).
    apply gquot_ind_beta_gcleq.
  Qed.
End gquot_rec.

Arguments gquot_rec {G} Y gclY gcleqY geY gconcatY {truncY}.

(** If the we have a family of sets, then we can simplify the induction principle. *)
Section gquot_ind_set.
  Variable (G : groupoid)
           (Y : gquot G → UU)
           (gclY : ∏ (a : G), Y(gcl G a))
           (gcleqY : ∏ (a₁ a₂ : G) (g : a₁ --> a₂),
               PathOver (gclY a₁) (gclY a₂) (gcleq G g))
           (truncY : ∏ (x : gquot G), isaset (Y x)).

  Definition gquot_ind_set : ∏ (g : gquot G), Y g.
  Proof.
    simple refine (gquot_ind Y gclY gcleqY _ _ _)
    ; intros.
    - apply path_globe_over_hset.
      apply truncY.
    - apply path_globe_over_hset.
      apply truncY.
    - apply hlevelntosn.
      apply truncY.
  Defined.

  Definition gquot_ind_set_beta_gcl (a : G)
    : gquot_ind_set (gcl G a) = gclY a
    := idpath _.

  Definition gquot_ind_set_beta_gcleq : ∏ (a₁ a₂ : G) (g : a₁ --> a₂),
      apd gquot_ind_set (gcleq G g)
      =
      gcleqY a₁ a₂ g.
  Proof.
    apply gquot_ind_beta_gcleq.
  Qed.
End gquot_ind_set.

Arguments gquot_ind_set {G} Y gclY gcleqY truncY.

(** If the we have a family of propositions, then we can simplify the induction principle. *)
Section gquot_ind_prop.
  Variable (G : groupoid)
           (Y : gquot G → UU)
           (gclY : ∏ (a : G), Y(gcl G a))
           (truncY : ∏ (x : gquot G), isaprop (Y x)).

  Definition gquot_ind_prop : ∏ (g : gquot G), Y g.
  Proof.
    simple refine (gquot_ind_set Y gclY _ _).
    - intros.
      apply PathOver_path_hprop.
      apply truncY.
    - intro.
      apply hlevelntosn.
      apply truncY.
  Qed.
End gquot_ind_prop.

Arguments gquot_ind_prop {G} Y gclY.

(** The double recursion principle.
    We use [gquot_rec], [gquot_ind_set] and [gquot_ind_prop] to define it.
 *)
Section gquot_double_rec.
  Variable (G₁ G₂ : groupoid)
           (Y : UU)
           (truncY : isofhlevel 3 Y).

  Variable (f : G₁ → G₂ → Y)
           (fr : ∏ (a : G₁) (b₁ b₂ : G₂),
               b₁ --> b₂ -> f a b₁ = f a b₂)
           (fre : ∏ (a : G₁) (b : G₂),
               fr a b b (identity b) = idpath _)
           (frc : ∏ (a : G₁) (b₁ b₂ b₃ : G₂)
                         (g₁ : b₁ --> b₂) (g₂ : b₂ --> b₃),
               fr a b₁ b₃ (g₁ · g₂)
               =
               (fr a b₁ b₂ g₁) @ (fr a b₂ b₃ g₂))
           (fl : ∏ (a₁ a₂ : G₁) (b : G₂),
               a₁ --> a₂ -> f a₁ b = f a₂ b)
           (fle : ∏ (a : G₁) (b : G₂),
               fl a a b (identity a) = idpath _)
           (flc : ∏ (a₁ a₂ a₃ : G₁) (b : G₂)
                         (g₁ : a₁ --> a₂) (g₂ : a₂ --> a₃),
               fl a₁ a₃ b (g₁ · g₂)
               =
               (fl a₁ a₂ b g₁) @ (fl a₂ a₃ b g₂))
           (fp : ∏ (a₁ a₂ : G₁) (b₁ b₂ : G₂)
                        (g₁ : a₁ --> a₂) (g₂ : b₁ --> b₂),
               square (fl a₁ a₂ b₂ g₁)
                      (fr a₁ b₁ b₂ g₂)
                      (fr a₂ b₁ b₂ g₂)
                      (fl a₁ a₂ b₁ g₁)).

  Definition gquot_double_rec' : gquot G₁ → gquot G₂ → Y.
  Proof.
    intros x y.
    simple refine (gquot_rec _ _ _ _ _ x).
    - refine (λ a, gquot_rec Y (f a) (fr a) (fre a) (frc a) y).
      exact truncY.
    - intros a₁ a₂ g₁ ; simpl.
      simple refine (gquot_ind_set (λ z, _) _ _ _ y).
      + exact (λ b, fl a₁ a₂ b g₁).
      + intros b₁ b₂ g₂.
        apply map_PathOver.
        refine (whisker_square (idpath _) _ _ (idpath _) _).
        * symmetry.
          apply gquot_rec_beta_gcleq.
        * symmetry.
          apply gquot_rec_beta_gcleq.
        * exact (fp a₁ a₂ b₁ b₂ g₁ g₂).
      + intro.
        exact (truncY _ _).
    - abstract
        (intros a ;
         simple refine (gquot_ind_prop (λ z, _) _ _ y) ;
         [ exact (λ b, fle a b)
         | exact (λ _, truncY _ _ _ _)]).
    - abstract
        (intros a₁ a₂ a₃ g ;
         simple refine (gquot_ind_prop (λ z, _) _ _ y) ;
         [ exact (λ b, flc a₁ a₂ a₃ b g)
         | intro ;
           use impred ; intro ;
           exact (truncY _ _ _ _)]).
    - exact truncY.
  Defined.

  Definition gquot_double_rec'_beta_l_gcleq
             {a₁ a₂ : G₁} (b : G₂)
             (g : a₁ --> a₂)
    : maponpaths (λ z, gquot_double_rec' z (gcl G₂ b)) (gcleq G₁ g)
      =
      fl a₁ a₂ b g.
  Proof.
    apply gquot_rec_beta_gcleq.
  Qed.

  Definition gquot_double_rec'_beta_r_gcleq
             (a : G₁) {b₁ b₂ : G₂}
             (g : b₁ --> b₂)
    : maponpaths (gquot_double_rec' (gcl G₁ a)) (gcleq G₂ g)
      =
      fr a b₁ b₂ g.
  Proof.
    apply (gquot_rec_beta_gcleq G₂).
  Qed.

  Definition gquot_double_rec : gquot G₁ × gquot G₂ → Y
    := uncurry gquot_double_rec'.

  Definition gquot_double_rec_point (a : G₁) (b : G₂)
    : gquot_double_rec (gcl G₁ a ,, gcl G₂ b) = f a b
    := idpath _.

  Definition gquot_double_rec_beta_gcleq
             {a₁ a₂ : G₁} {b₁ b₂ : G₂}
             (g₁ : a₁ --> a₂) (g₂ : b₁ --> b₂)
    : maponpaths gquot_double_rec (pathsdirprod (gcleq G₁ g₁) (gcleq G₂ g₂))
      =
      fl a₁ a₂ b₁ g₁ @ fr a₂ b₁ b₂ g₂.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (maponpaths (λ z, z @ _) (gquot_rec_beta_gcleq G₁ _ _ _ _ _ _ _ _ _) @ _).
    exact (maponpaths (λ z, _ @ z) (gquot_rec_beta_gcleq G₂ _ _ _ _ _ _ _ _ _)).
  Qed.

  Definition gquot_double_rec_beta_l_gcleq
             {a₁ a₂ : G₁} (b : G₂)
             (g : a₁ --> a₂)
    : maponpaths gquot_double_rec (pathsdirprod (gcleq G₁ g) (idpath (gcl G₂ b)))
      =
      fl a₁ a₂ b g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (maponpaths (λ z, z @ _) (gquot_rec_beta_gcleq G₁ _ _ _ _ _ _ _ _ _) @ _).
    apply pathscomp0rid.
  Qed.
  
  Definition gquot_double_rec_beta_r_gcleq
             (a : G₁) {b₁ b₂ : G₂}
             (g : b₁ --> b₂)
    : maponpaths gquot_double_rec (pathsdirprod (idpath (gcl G₁ a)) (gcleq G₂ g))
      =
      fr a b₁ b₂ g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    exact (maponpaths (λ z, _ @ z) (gquot_rec_beta_gcleq G₂ _ _ _ _ _ _ _ _ _)).
  Qed.
End gquot_double_rec.

Arguments gquot_double_rec {G₁ G₂} Y {_ _}.
Arguments gquot_double_rec' {G₁ G₂} Y {_ _}.
Arguments gquot_double_rec_beta_gcleq {G₁ G₂} Y {_ _}.

(** Double induction over a family of sets.
    We use the same trick as for double recursion.
 *)
Section gquot_double_ind_set.
  Variable (G₁ G₂ : groupoid)
           (Y : gquot G₁ → gquot G₂ → UU)
           (Yisaset : ∏ (a : gquot G₁) (b : gquot G₂), isaset (Y a b)).
  
  Variable (f : ∏ (a : G₁) (b : G₂), Y (gcl G₁ a) (gcl G₂ b))
           (fr : ∏ (a : G₁) (b₁ b₂ : G₂) (g : b₁ --> b₂),
                 PathOver (f a b₁) (f a b₂) (gcleq G₂ g))
           (fl : ∏ (a₁ a₂ : G₁) (b : G₂) (g : a₁ --> a₂),
                 @PathOver
                   _ _ _
                   (λ z : gquot G₁, Y z (gcl G₂ b))
                   (f a₁ b)
                   (f a₂ b)
                   (gcleq G₁ g)).

  Definition gquot_double_ind_set : ∏ (a : gquot G₁) (b : gquot G₂), Y a b.
  Proof.
    intros a b.
    revert a.
    use gquot_ind_set.
    - intro a.
      revert b.
      use gquot_ind_set.
      + exact (f a).
      + exact (fr a).
      + intro ; apply Yisaset.
    - abstract
        (intros a₁ a₂ g ;
         revert b ;
         use gquot_ind_prop ;
         [ exact (λ b, fl a₁ a₂ b g)
         | intro ;
           apply PathOver_hprop ;
           intro ;
           apply Yisaset]).
    - intro x.
      apply Yisaset.
  Defined.
End gquot_double_ind_set.

Arguments gquot_double_ind_set {G₁ G₂} Y {_ _}.

(** Double induction over a family of propositions.
    We use the same trick as before.
 *)
Section gquot_double_ind_prop.
  Variable (G₁ G₂ : groupoid)
           (Y : gquot G₁ → gquot G₂ → UU)
           (Yisaprop : ∏ (a : gquot G₁) (b : gquot G₂), isaprop (Y a b)).
  
  Variable (f : ∏ (a : G₁) (b : G₂), Y (gcl G₁ a) (gcl G₂ b)).
  
  Definition gquot_double_ind_prop : ∏ (a : gquot G₁) (b : gquot G₂), Y a b.
  Proof.
    intros x y.
    simple refine (gquot_ind_prop (λ z, _) _ _ x).
    + simple refine (λ a, gquot_ind_prop (λ z, _) (f a) _ y).
      intro ; simpl.
      apply Yisaprop.
    + intro ; simpl.
      apply Yisaprop.
  Defined.
End gquot_double_ind_prop.

Arguments gquot_double_ind_prop {G₁ G₂} Y.

(** A special instance of double recursion for defining set-relations.
    This requires univalence, because we need to give equalities in [hSet].
    These equalities are made with [path_hset] and two functions need to be given.
    For the higher coherencies, these functions need to satisfy some laws.
 *)
Section gquot_relation.
  Variable (G₁ G₂ : groupoid)
           (R : G₁ → G₂ → hSet)
           (fl : ∏ (a₁ a₂ : G₁) (b : G₂), a₁ --> a₂ → R a₁ b → R a₂ b)
           (fr : ∏ (a : G₁) (b₁ b₂ : G₂), b₁ --> b₂ → R a b₁ → R a b₂).
  Variable (fl_isweq : ∏ (a₁ a₂ : G₁) (b : G₂) (g : a₁ --> a₂), isweq (fl a₁ a₂ b g))
           (fr_isweq : ∏ (a : G₁) (b₁ b₂ : G₂) (g : b₁ --> b₂), isweq (fr a b₁ b₂ g)).

  Variable (fl_id : ∏ (a : G₁) (b : G₂), homot (fl a a b (identity a)) (λ z, z))
           (fl_comp : ∏ (a₁ a₂ a₃ : G₁) (b : G₂)
                        (g₁ : a₁ --> a₂) (g₂ : a₂ --> a₃),
                      homot
                        (fl a₁ a₃ b (g₁ · g₂))
                        (fl a₂ a₃ b g₂ ∘ (fl a₁ a₂ b g₁))%functions)
           (fr_id : ∏ (a : G₁) (b : G₂), homot (fr a b b (identity b)) (λ z, z))
           (fr_comp : ∏ (a : G₁) (b₁ b₂ b₃ : G₂)
                        (g₁ : b₁ --> b₂) (g₂ : b₂ --> b₃),
                      homot
                        (fr a b₁ b₃ (g₁ · g₂))
                        (fr a b₂ b₃ g₂ ∘ (fr a b₁ b₂ g₁))%functions)
           (fc : ∏ (a₁ a₂ : G₁) (b₁ b₂ : G₂)
                   (g₁ : a₁ --> a₂) (g₂ : b₁ --> b₂),
                 (homot
                   (fl a₁ a₂ b₂ g₁ ∘ fr a₁ b₁ b₂ g₂)
                   (fr a₂ b₁ b₂ g₂ ∘ fl a₁ a₂ b₁ g₁))%functions
           ).

  Definition fl_weq
    : ∏ (a₁ a₂ : G₁) (b : G₂), a₁ --> a₂ → R a₁ b ≃ R a₂ b.
  Proof.
    intros a₁ a₂ b g.
    use make_weq.
    - exact (fl a₁ a₂ b g).
    - exact (fl_isweq a₁ a₂ b g).
  Defined.

  Definition fr_weq
    : ∏ (a : G₁) (b₁ b₂ : G₂), b₁ --> b₂ → R a b₁ ≃ R a b₂.
  Proof.
    intros a b₁ b₂ g.
    use make_weq.
    - exact (fr a b₁ b₂ g).
    - exact (fr_isweq a b₁ b₂ g).
  Defined.

  Definition path_hset_fl_refl
             (a : G₁) (b : G₂)
    : @path_HLevel 2 _ _ (fl_weq a a b (identity a)) = idpath _.
  Proof.
    rewrite <- path_HLevel_id.
    apply path_HLevel_eq.
    apply fl_id.
  Qed.

  Definition path_hset_fl_trans
             (a₁ a₂ a₃ : G₁) (b : G₂)
             (g₁ : a₂ --> a₃) (g₂ : a₁ --> a₂)
    : @path_HLevel 2 _ _ (fl_weq a₁ a₃ b (g₂ · g₁))
      =
      (@path_HLevel 2 _ _ (fl_weq a₁ a₂ b g₂))
        @
        @path_HLevel 2 _ _ (fl_weq a₂ a₃ b g₁).
  Proof.
    rewrite <- path_HLevel_comp.
    apply path_HLevel_eq.
    apply fl_comp.
  Qed.
  
  Definition path_hset_fr_refl
             (a : G₁) (b : G₂)
    : @path_HLevel 2 _ _ (fr_weq a b b (identity b)) = idpath _.
  Proof.
    rewrite <- path_HLevel_id.
    apply path_HLevel_eq.
    apply fr_id.
  Qed.

  Definition path_hset_fr_trans
             (a : G₁) (b₁ b₂ b₃ : G₂)
             (g₁ : b₂ --> b₃) (g₂ : b₁ --> b₂)
    : @path_HLevel 2 _ _ (fr_weq a b₁ b₃ (g₂ · g₁))
      =
      (@path_HLevel 2 _ _ (fr_weq a b₁ b₂ g₂))
        @
        @path_HLevel 2 _ _ (fr_weq a b₂ b₃ g₁).
  Proof.
    rewrite <- path_HLevel_comp.
    apply path_HLevel_eq.
    apply fr_comp.
  Qed.

  Definition path_hset_fl_fr
             (a₁ a₂ : G₁) (b₁ b₂ : G₂)
             (g₁ : a₁ --> a₂)
             (g₂ : b₁ --> b₂)
    : (@path_HLevel 2 _ _ (fr_weq a₁ b₁ b₂ g₂))
        @
        @path_HLevel 2 _ _ (fl_weq a₁ a₂ b₂ g₁)
      =
      (@path_HLevel 2 _ _ (fl_weq a₁ a₂ b₁ g₁))
        @
        @path_HLevel 2 _ _ (fr_weq a₂ b₁ b₂ g₂).
  Proof.
    refine (!(path_HLevel_comp _ _) @ _ @ path_HLevel_comp _ _).
    apply path_HLevel_eq ; cbn.
    apply fc.
  Qed.

  Definition gquot_relation : gquot G₁ → gquot G₂ → hSet.
  Proof.
    simple refine (gquot_double_rec' _ _ _ _ _ _ _ _).
    - apply isofhlevel_HLevel.
    - exact R.
    - exact (λ a b₁ b₂ g, @path_HLevel 2 _ _ (fr_weq a b₁ b₂ g)).
    - exact path_hset_fr_refl.
    - intros.
      apply path_hset_fr_trans.
    - exact (λ a₁ a₂ b g, @ path_HLevel 2 _ _ (fl_weq a₁ a₂ b g)).
    - exact path_hset_fl_refl.
    - intros.
      apply path_hset_fl_trans.
    - intros a₁ a₂ b₁ b₂ g₁ g₂.
      apply path_hset_fl_fr.
  Defined.

  Definition gquot_relation_gcl_gcl (a : G₁) (b : G₂)
    : gquot_relation (gcl G₁ a) (gcl G₂ b) = R a b
    := idpath _.

  Definition gquot_relation_beta_l_gcleq
             {a₁ a₂ : G₁} (b : G₂) (g : a₁ --> a₂)
    : maponpaths (λ z, gquot_relation z (gcl G₂ b)) (gcleq G₁ g)
      =
      @path_HLevel 2 _ _ (fl_weq a₁ a₂ b g).
  Proof.
    exact (gquot_double_rec'_beta_l_gcleq G₁ G₂ hSet _ R _ _ _ _ _ _ _ b g).
  Qed.

  Definition gquot_relation_beta_r_gcleq
             (a : G₁) {b₁ b₂ : G₂} (g : b₁ --> b₂)
    : maponpaths (gquot_relation (gcl G₁ a)) (gcleq G₂ g)
      =
      @path_HLevel 2 _ _ (fr_weq a b₁ b₂ g).
  Proof.
    exact (gquot_double_rec'_beta_r_gcleq G₁ G₂ hSet _ R _ _ _ _ _ _ _ a g).
  Qed.
End gquot_relation.
