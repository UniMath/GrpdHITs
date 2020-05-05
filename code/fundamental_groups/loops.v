(**
We show that the path space of the circle is the integers
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import prelude.all.
Require Import initial_grpd_alg.is_initial.

Local Open Scope cat.

(** Induction for integers *)
Definition hz_ind
           {Y : hz → UU}
           (Yz : Y (0%hz))
           (Yplus : ∏ (n : nat), Y (nattohz n) → Y (nattohz (S n)))
           (Ymin : ∏ (n : nat), Y (toℤneg n) → Y (toℤneg (S n)))
           (z : hz)
  : Y z.
Proof.
  pose (hz_to_normal_form z) as znf.
  induction znf as [zpos | zneg].
  - induction zpos as [n p].
    refine (transportf Y p _).
    clear p z.
    induction n.
    + exact Yz.
    + exact (Yplus _ IHn).
  - induction zneg as [n p].
    refine (transportf Y p _).
    clear p z.
    induction n.
    + apply Ymin.
      apply Yz.
    + apply Ymin.
      exact IHn.
Defined.

(** The UMP for 1-cells *)
Definition toℤneg_S
           (n : nat)
  : toℤneg (S n) = (toℤneg n - 1)%hz.
Proof.
  unfold toℤneg.
  rewrite <- !hzsign_nattohz.
  rewrite nattohzandS.
  rewrite hzminusplus.
  rewrite hzpluscomm.
  apply idpath.
Qed.

Definition morph_power_nat
           {C : precategory}
           {x : C}
           (f : x --> x)
           (n : nat)
  : x --> x.
Proof.
  induction n as [|n g].
  - exact (identity x).
  - exact (f · g).
Defined.

Definition morph_power
           {C : groupoid}
           {x : C}
           (f : x --> x)
           (z : hz)
  : x --> x.
Proof.
  pose (hz_to_normal_form z) as znf.
  induction znf as [(n , pos) | (n , neg)].
  - exact (morph_power_nat f n).
  - exact (morph_power_nat (grpd_inv f) (S n)).
Defined.

Local Notation "f ^ z" := (morph_power f z).

Definition morph_power_pos
           {C : groupoid}
           {x : C}
           (f : x --> x)
           (n : nat)
  : f ^ (nattohz n) = morph_power_nat f n.
Proof.
  induction n ; apply idpath.
Qed.

Definition morph_power_neg
           {C : groupoid}
           {x : C}
           (f : x --> x)
           (n : nat)
  : f ^ (toℤneg n) = morph_power_nat (grpd_inv f) n.
Proof.
  induction n as [ | n IHn].
  - apply idpath.
  - simpl.
    rewrite toℤneg_S.
    unfold hzminus.
    rewrite hzpluscomm.
    refine (maponpaths (λ z, _ · morph_power_nat (grpd_inv f) z) _).
    simpl.
    apply natminuseqn.
Qed.

Definition morph_power_zero
           {C : groupoid}
           {x : C}
           (f : x --> x)
  : f ^ (0%hz) = identity x.
Proof.
  apply idpath.
Qed.

Definition morp_power_suc_pred
           {C : groupoid}
           {x : C}
           (f : x --> x)
           (z : hz)
  : f ^ (1 + z)%hz = f · f^z
  × f ^ (-(1) + z)%hz = grpd_inv f · f^z.
Proof.
  revert z.
  use hz_ind.
  - simpl.
    split.
    + rewrite hzplusr0, morph_power_zero, id_right.
      apply id_right.
    + rewrite hzplusr0, morph_power_zero, id_right.
      apply id_right.
  - simpl.
    intros n IHn.
    induction IHn as [IHnplus IHnmin].
    split.
    + apply idpath.
    + rewrite nattohzandS.
      rewrite <- hzplusassoc.
      rewrite hzlminus.
      rewrite hzplusl0.
      rewrite IHnplus.
      apply move_grpd_inv_right.
      apply idpath.
  - simpl ; intros n IHn.
    induction IHn as [IHnplus IHnmin].
    split.
    + rewrite !toℤneg_S.
      unfold hzminus.
      rewrite hzpluscomm.
      rewrite hzplusassoc.
      rewrite hzlminus.
      rewrite hzplusr0.
      rewrite hzpluscomm.
      rewrite IHnmin.
      rewrite assoc.
      refine (!(id_left _) @ _).
      apply maponpaths_2.
      use move_grpd_inv_left.
      exact (!(id_left _)).
    + rewrite !toℤneg_S.
      unfold hzminus.
      refine (!_).
      rewrite hzpluscomm.
      rewrite IHnmin.
      rewrite morph_power_neg.
      apply idpath.
Qed.

  
Definition morp_power_suc
           {C : groupoid}
           {x : C}
           (f : x --> x)
           (z : hz)
  : f ^ (1 + z)%hz = f · f^z.
Proof.
  exact (pr1 (morp_power_suc_pred f z)).
Qed.

Definition morph_power_pred
           {C : groupoid}
           {x : C}
           (f : x --> x)
           (z : hz)
  : f ^ (-(1) + z)%hz = grpd_inv f · f^z.
Proof.
  exact (pr2 (morp_power_suc_pred f z)).
Qed.

Definition morph_power_plus
           {C : groupoid}
           {x : C}
           (f : x --> x)
           (z₁ z₂ : hz)
  : f ^ (z₁ + z₂)%hz
    =
    f ^ z₁ · f ^ z₂.
Proof.
  revert z₁ z₂.
  use hz_ind.
  - intro z.
    simpl.
    rewrite morph_power_zero, id_left, hzplusl0.
    apply idpath.
  - intros n IHn z.
    cbn -[hz] in IHn ; cbn -[hz].
    rewrite nattohzandS.
    rewrite hzplusassoc.
    cbn -[hz].
    rewrite !morp_power_suc.
    rewrite assoc'.
    apply maponpaths.
    apply IHn.
  - intros n IHn z.
    cbn -[hz] in IHn ; cbn -[hz].
    rewrite !toℤneg_S.
    unfold hzminus.
    rewrite hzplusassoc.
    rewrite hzpluscomm.
    rewrite hzplusassoc.
    rewrite morph_power_pred.
    rewrite hzpluscomm.
    rewrite IHn.
    rewrite assoc.
    apply maponpaths_2.
    rewrite hzpluscomm.
    rewrite morph_power_pred.
    apply idpath.
Qed.

Definition power_commute_one
           {C : groupoid}
           {x : C}
           (f g : x --> x)
           (p : f · g = g · f)
  : ∏ (m : hz), f · g ^ m = g ^ m · f.
Proof.
  use hz_ind.
  - cbn -[hz].
    exact (id_right _ @ !(id_left _)).
  - cbn -[hz] ; intros m IHm.
    rewrite !nattohzandS.
    rewrite !morp_power_suc.
    rewrite assoc.
    rewrite p.
    rewrite !assoc'.
    apply maponpaths.
    apply IHm.
  - cbn -[hz] ; intros m IHm.
    rewrite !toℤneg_S.
    unfold hzminus.
    rewrite hzpluscomm.
    rewrite morph_power_pred.
    rewrite assoc'.
    rewrite <- IHm.
    rewrite !assoc.
    apply maponpaths_2.
    use move_grpd_inv_right.
    rewrite assoc.
    use move_grpd_inv_left.
    exact (!p).
Qed.

Definition power_commute
           {C : groupoid}
           {x : C}
           (f g : x --> x)
           (p : f · g = g · f)
  : ∏ (n m : hz), f ^ n · g ^ m = g ^ m · f ^ n.
Proof.
  use hz_ind.
  - cbn -[hz].
    intro m.
    exact (id_left _ @ !(id_right _)).
  - cbn -[hz] ; intros n IHn m.
    rewrite !nattohzandS.
    rewrite !morp_power_suc.
    rewrite assoc'.
    rewrite IHn.
    rewrite !assoc.
    apply maponpaths_2.
    apply power_commute_one.
    exact p.
  - cbn -[hz] ; intros n IHn m.
    rewrite !toℤneg_S.
    unfold hzminus.
    rewrite hzpluscomm.
    rewrite morph_power_pred.
    rewrite assoc'.
    rewrite IHn.
    rewrite !assoc.
    apply maponpaths_2.
    apply power_commute_one.
    refine (!_).
    use move_grpd_inv_right.
    rewrite assoc.
    use move_grpd_inv_left.
    exact p.
Qed.

Definition power_swap
           {C : groupoid}
           {x y : C}
           {f : x --> x}
           {g : x --> y}
           {h : y --> y}
           (p : f · g = g · h)
  : ∏ (n : hz), f ^ n · g = g · h ^ n.
Proof.
  use hz_ind.
  - cbn -[hz].
    exact (id_left _ @ !(id_right _)).
  - cbn -[hz] ; intros m IHm.
    rewrite !nattohzandS.
    rewrite !morp_power_suc.
    rewrite assoc.
    rewrite <- p.
    rewrite !assoc'.
    apply maponpaths.
    apply IHm.
  - cbn -[hz] ; intros m IHm.
    rewrite !toℤneg_S.
    unfold hzminus.
    rewrite hzpluscomm.
    rewrite morph_power_pred.
    rewrite assoc'.
    rewrite IHm.
    rewrite !assoc.
    rewrite morph_power_plus.
    rewrite assoc.
    apply maponpaths_2.
    refine (!_).
    use move_grpd_inv_right.
    cbn.
    rewrite id_right.
    rewrite assoc.
    use move_grpd_inv_left.
    exact p.
Qed.
    
Definition functor_on_morpower
           {C D : groupoid}
           (F : C ⟶ D)
           {x : C}
           (f : x --> x)
           (n : hz)
  : #F (f ^ n) = (#F f) ^ n.
Proof.
  revert n.
  use hz_ind.
  - apply functor_id.
  - simpl.
    intros n IHn.
    rewrite !nattohzandS.
    rewrite !morp_power_suc.
    rewrite functor_comp.
    apply maponpaths.
    exact IHn.
  - simpl.
    intros n IHn.
    rewrite !toℤneg_S.
    unfold hzminus.
    rewrite hzpluscomm.
    rewrite !morph_power_pred.
    rewrite functor_comp.
    rewrite IHn.
    apply maponpaths_2.
    refine (_ @ id_left _).
    use move_grpd_inv_left.
    rewrite <- functor_comp.
    refine (!(functor_id _ _) @ _).
    apply maponpaths.
    use move_grpd_inv_right.
    exact (!(id_right _)).
Qed.

(** Double power *)
Definition double_power
           {C : groupoid}
           {x : C}
           (f g : x --> x)
           (n m : hz)
  : x --> x
  := f ^ n · g ^ m.

Definition functor_on_double_power
           {C D : groupoid}
           (F : C ⟶ D)
           {x : C}
           (f g : x --> x)
           (n m : hz)
  : #F (double_power f g n m)
    =
    double_power (#F f) (#F g) n m.
Proof.
  unfold double_power.
  rewrite functor_comp.
  rewrite !functor_on_morpower.
  apply idpath.
Qed.

Definition double_power_swap
           {C : groupoid}
           {x y : C}
           {f₁ f₂ : x --> x}
           {g : x --> y}
           {h₁ h₂ : y --> y}
           (p : f₁ · g = g · h₁)
           (q : f₂ · g = g · h₂)
           (n m : hz)
  : double_power f₁ f₂ n m · g = g · h₁ ^ n · h₂ ^ m.
Proof.
  unfold double_power.
  rewrite assoc'.
  etrans.
  {
    apply maponpaths.
    exact (power_swap q m).
  }
  rewrite assoc.
  etrans.
  {
    apply maponpaths_2.
    exact (power_swap p n).
  }
  apply idpath.
Qed.
