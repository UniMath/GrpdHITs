(** Here we define W-types of polynomials *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import displayed_algebras.displayed_algebra.

Declare Scope container_scope.

Definition transportf_depfun
           {A B : UU}
           {Y : A → UU}
           {Z : B → UU}
           (f : A → B)
           (ff : ∏ (a : A), Y a → Z(f a))
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (y : Y a₁)
  : transportf
      Z
      (maponpaths f p)
      (ff a₁ y)
    =
    ff a₂ (transportf Y p y).
Proof.
  induction p.
  apply idpath.
Defined.

Definition transportf_fun_space
           {X : UU}
           {Y : X → UU}
           {Z : UU}
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           (f : Y x₁ → Z)
           (y : Y x₂)
  : transportf (λ x, Y x → Z) p f y
    =
    f (transportb Y p y).
Proof.
  induction p.
  apply idpath.
Defined.
           
Definition sum_fam
           {X₁ X₂ : UU}
           (Y₁ : X₁ → UU)
           (Y₂ : X₂ → UU)
  : X₁ ⨿ X₂ → UU.
Proof.
  intro z.
  induction z as [z | z].
  - exact (Y₁ z).
  - exact (Y₂ z).
Defined.

Definition transportf_maponpaths_inl
           {X₁ X₂ : UU}
           (Y₁ : X₁ → UU)
           (Y₂ : X₂ → UU)
           {x₁ x₂ : X₁}
           (p : x₁ = x₂)
           (y : sum_fam Y₁ Y₂ (inl x₁))
  : transportf
      (λ x, sum_fam Y₁ Y₂ x)
      (maponpaths inl p)
      y
    =
    transportf Y₁ p y.
Proof.
  induction p.
  apply idpath.
Defined.

Definition transportf_maponpaths_inr
           {X₁ X₂ : UU}
           (Y₁ : X₁ → UU)
           (Y₂ : X₂ → UU)
           {x₁ x₂ : X₂}
           (p : x₁ = x₂)
           (y : sum_fam Y₁ Y₂ (inr x₁))
  : transportf
      (λ x, sum_fam Y₁ Y₂ x)
      (maponpaths inr p)
      y
    =
    transportf Y₂ p y.
Proof.
  induction p.
  apply idpath.
Defined.

Definition transportb_maponpaths_pathsdirprod
           {X₁ X₂ : UU}
           (Y₁ : X₁ → UU)
           (Y₂ : X₂ → UU)
           {x₁ x₂ : X₁} {y₁ y₂ : X₂}
           (p : x₁ = x₂) (q : y₁ = y₂)
           (z : Y₁ x₂ ⨿ Y₂ y₂)
  : transportb
      (λ x, Y₁ (pr1 x) ⨿ Y₂ (pr2 x))
      (pathsdirprod p q)
      z
    =
    coprod_rect
      _
      (λ w, inl (transportb Y₁ p w))
      (λ w, inr (transportb Y₂ q w))
      z.
Proof.
  induction p, q.
  induction z ; apply idpath.
Defined.

Definition transportf_prod
           {A B : UU}
           {Y : A → UU}
           {Z : B → UU}
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           {b₁ b₂ : B}
           (q : b₁ = b₂)
           (y : Y a₁)
           (z : Z b₁)
  : transportf
      (λ (x : A × B), Y (pr1 x) × Z (pr2 x))
      (pathsdirprod p q)
      (y ,, z)
    =
    transportf Y p y ,, transportf Z q z.
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.

(** Basics of containers *)
Record container :=
  mkContainer
    {
      shapes : UU ;
      positions : shapes → UU
    }.

(** Builder *)
Definition make_container
           (S : UU)
           (P : S → UU)
  : container.
Proof.
  use mkContainer.
  - exact S.
  - exact P.
Defined.

Notation "S ◅ P" := (make_container S P) (at level 60) : container_scope.

Local Open Scope container_scope.

(** Constructions of containers *)
Definition constant_container
           (A : UU)
  : container
  := A ◅ (λ _, ∅).

Definition identity_container
  : container
  := unit ◅ (λ _, unit).

Definition sum_container
           (C₁ C₂ : container)
  : container
  := (shapes C₁ ⨿ shapes C₂) ◅ (coprod_rect _ (positions C₁) (positions C₂)).

Definition prod_container
           (C₁ C₂ : container)
  : container
  := (shapes C₁ × shapes C₂) ◅ (λ z, positions C₁ (pr1 z) ⨿ positions C₂ (pr2 z)).

Definition poly_container
           (P : poly_code)
  : container.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (constant_container A).
  - exact identity_container.
  - exact (sum_container IHP₁ IHP₂).
  - exact (prod_container IHP₁ IHP₂).
Defined.

(** Interpretation of containers *)
Definition interpret_container
           (C : container)
           (X : UU)
  : UU
  := ∑ (s : shapes C), positions C s → X.

Notation "⟦ C ⟧ X" := (interpret_container C X) (at level 70) : container_scope.

Definition cpair
           (C : container)
           {X : UU}
           (s : shapes C)
           (p : positions C s → X)
  : ⟦ C ⟧ X
  := s ,, p.

Definition interpret_map
           (C : container)
           {X Y : UU}
           (f : X → Y)
  : ⟦ C ⟧ X → ⟦ C ⟧ Y
  := λ z, cpair C (pr1 z) (λ q, f (pr2 z q)).

Definition interpret_map_id
           (C : container)
           (X : UU)
           (x : ⟦ C ⟧ X)
  : interpret_map C (idfun X) x = x
  := idpath _.

Definition interpret_map_comp
           (C : container)
           {X Y Z : UU}
           (f : X → Y) (g : Y → Z)
           (x : ⟦ C ⟧ X)
  : interpret_map C (λ z, g(f z)) x
    =
    interpret_map C g (interpret_map C f x)
  := idpath _.

(** Interpretation of the constructions (up to equivalence) *)

(** Constant *)
Definition interpret_constant
           (A : UU)
           (X : UU)
  : ⟦ constant_container A ⟧ X → A
  := λ z, pr1 z.

Definition to_interpret_constant
           (A : UU)
           (X : UU)
  : A → ⟦ constant_container A ⟧ X
  := λ a, a ,, fromempty.

Definition interpret_constant_weq
           (A : UU)
           (X : UU)
  : ⟦ constant_container A ⟧ X ≃ A.
Proof.
  use make_weq.
  - exact (interpret_constant A X).
  - use isweq_iso.
    + exact (to_interpret_constant A X).
    + intros x.
      use total2_paths_f.
      * exact (idpath _).
      * use funextsec.
        intro z ; induction z.
    + intros x.
      apply idpath.
Defined.

(** Identity *)
Definition interpret_identity
           (X : UU)
  : ⟦ identity_container ⟧ X → X
  := λ z, pr2 z tt.

Definition to_interpret_identity
           (X : UU)
  : X → ⟦ identity_container ⟧ X
  := λ z, tt ,, (λ _, z).

Definition interpret_identity_weq
           (X : UU)
  : ⟦ identity_container ⟧ X ≃ X.
Proof.
  use make_weq.
  - exact (interpret_identity X).
  - use isweq_iso.
    + exact (to_interpret_identity X).
    + intros x.
      induction x as [sx px].
      induction sx.
      apply (maponpaths (λ z, tt ,, z)).
      use funextsec.
      intro z.
      induction z.
      apply idpath.
    + intro y.
      apply idpath.
Defined.

(** Sum *)
Definition interpret_sum
           (C₁ C₂ : container)
           (X : UU)
  : ⟦ sum_container C₁ C₂ ⟧ X
    →
    (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X).
Proof.
  intros z.
  induction z as [sz pz].
  induction sz as [sz | sz].
  + exact (inl (sz ,, pz)).
  + exact (inr (sz ,, pz)).
Defined.

Definition to_interpret_sum
           (C₁ C₂ : container)
           (X : UU)
  : (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X)
    →
    ⟦ sum_container C₁ C₂ ⟧ X.
Proof.
  intros z.
  induction z as [z | z].
  - exact (inl (pr1 z) ,, pr2 z).
  - exact (inr (pr1 z) ,, pr2 z).
Defined.

Definition interpret_sum_weq
           (C₁ C₂ : container)
           (X : UU)
  : ⟦ sum_container C₁ C₂ ⟧ X
    ≃
    (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X).
Proof.
  use make_weq.
  - exact (interpret_sum C₁ C₂ X).
  - use isweq_iso.
    + exact (to_interpret_sum C₁ C₂ X).
    + intro z.
      induction z as [sz pz].
      induction sz as [sz | sz].
      * apply idpath.
      * apply idpath.
    + intros z.
      induction z as [z | z].
      * apply idpath.
      * apply idpath.
Defined.

(** The product *)
Definition interpret_prod
           (C₁ C₂ : container)
           (X : UU)
  : ⟦ prod_container C₁ C₂ ⟧ X
    →
    (⟦ C₁ ⟧ X) × (⟦ C₂ ⟧ X).
Proof.
  intros z.
  refine ((pr11 z ,, _) ,, (pr21 z ,, _)).
  - exact (λ q, pr2 z (inl q)).
  - exact (λ q, pr2 z (inr q)).
Defined.

Definition to_interpret_prod
           (C₁ C₂ : container)
           (X : UU)
  : (⟦ C₁ ⟧ X) × (⟦ C₂ ⟧ X)
    →
    ⟦ prod_container C₁ C₂ ⟧ X
  := λ z, (pr11 z ,, pr12 z) ,, coprod_rect _ (λ q, pr21 z q) (λ q, pr22 z q).

Definition interpret_prod_weq
           (C₁ C₂ : container)
           (X : UU)
  : ⟦ prod_container C₁ C₂ ⟧ X
    ≃
    (⟦ C₁ ⟧ X) × (⟦ C₂ ⟧ X).
Proof.
  use make_weq.
  - exact (interpret_prod C₁ C₂ X).
  - use isweq_iso.
    + exact (to_interpret_prod C₁ C₂ X).
    + intro z.
      use total2_paths_f.
      * apply idpath.
      * use funextsec.
        intro q.
        induction q.
        ** apply idpath.
        ** apply idpath.
    + intros z.
      apply idpath.
Defined.

(** Polynomials *)
Definition interpret_poly
           (P : poly_code)
           (X : UU)
  : ⟦ poly_container P ⟧ X
    →
    poly_act P X.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply interpret_constant.
  - apply interpret_identity.
  - intro z.
    induction (interpret_sum (poly_container P₁) (poly_container P₂) X z) as [q | q].
    + exact (inl (IHP₁ q)).
    + exact (inr (IHP₂ q)).
  - intro z.
    pose (interpret_prod (poly_container P₁) (poly_container P₂) X z) as q.
    exact (IHP₁ (pr1 q) ,, IHP₂ (pr2 q)).
Defined.

Definition to_interpret_poly
           (P : poly_code)
           (X : UU)
  : poly_act P X
    →
    ⟦ poly_container P ⟧ X.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply to_interpret_constant.
  - apply to_interpret_identity.
  - intro z.
    induction z as [z | z].
    + exact (to_interpret_sum
               (poly_container P₁) (poly_container P₂) X
               (inl (IHP₁ z))).
    + exact (to_interpret_sum
               (poly_container P₁) (poly_container P₂) X
               (inr (IHP₂ z))).
  - exact (λ z, to_interpret_prod
                  (poly_container P₁) (poly_container P₂) X
                  (IHP₁ (pr1 z) ,, IHP₂ (pr2 z))).
Defined.

Definition to_interpret_poly_interpret_poly'
           (P : poly_code)
           (X : UU)
           (x : ⟦ poly_container P ⟧ X)
  : to_interpret_poly P X (interpret_poly P X x) = x.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ]
  ; induction x as [i x].
  - use total2_paths_f.
    + apply idpath.
    + use funextsec ; cbn.
      intro z ; induction z.
  - induction i.
    use total2_paths_f.
    + apply idpath.
    + use funextsec.
      intro z.
      induction z.
      apply idpath.
  - induction i as [i | i].
    + use total2_paths_f.
      * exact (maponpaths inl (maponpaths pr1 (IHP₁ (i ,, x)))).
      * use funextsec.
        intro z.
        refine (_ @ eqtohomot (fiber_paths (IHP₁ (i ,, x))) z).
        refine (transportf_fun_space _ _ _ @ _ @ !(transportf_fun_space _ _ _)).
        apply maponpaths.
        refine (_ @ transportf_maponpaths_inl _ _ _ _).
        apply transportf_paths.
        refine (!_).
        exact (maponpathsinv0 inl _).
    + use total2_paths_f.
      * exact (maponpaths inr (maponpaths pr1 (IHP₂ (i ,, x)))).
      * simpl.
        use funextsec.
        intro z.
        refine (_ @ eqtohomot (fiber_paths (IHP₂ (i ,, x))) z).
        refine (transportf_fun_space _ _ _ @ _ @ !(transportf_fun_space _ _ _)).
        apply maponpaths.
        refine (_ @ transportf_maponpaths_inr _ _ _ _).
        apply transportf_paths.
        refine (!_).
        exact (maponpathsinv0 inr _).
  - use total2_paths_f.
    + exact (pathsdirprod (maponpaths pr1 (IHP₁ _)) (maponpaths pr1 (IHP₂ _))).
    + use funextsec.
      intro z.
      refine (transportf_fun_space _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        simpl.
        apply transportb_maponpaths_pathsdirprod.
      }
      induction z as [z | z] ; simpl.
      * refine (_ @ eqtohomot
                      (fiber_paths
                         (IHP₁
                            (cpair
                               (poly_container P₁)
                               (pr1 i)
                               (λ q, x (inl q)))))
                      z).
        exact (!(transportf_fun_space _ _ _)).
      * refine (_ @ eqtohomot
                      (fiber_paths
                         (IHP₂
                            (cpair
                               (poly_container P₂)
                               (pr2 i)
                               (λ q, x (inr q)))))
                      z).
        exact (!(transportf_fun_space _ _ _)).
Defined.

Definition interpret_poly_to_interpret_poly
           (P : poly_code)
           (X : UU)
           (y : poly_act P X)
  : interpret_poly P X (to_interpret_poly P X y) = y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction y as [y | y].
    + exact (maponpaths inl (IHP₁ y)).
    + exact (maponpaths inr (IHP₂ y)).
  - exact (pathsdirprod (IHP₁ (pr1 y)) (IHP₂ (pr2 y))).
Defined.

Definition interpret_poly_weq
           (P : poly_code)
           (X : UU)
  : ⟦ poly_container P ⟧ X
    ≃
    poly_act P X.
Proof.
  use make_weq.
  - exact (interpret_poly P X).
  - use isweq_iso.
    + exact (to_interpret_poly P X).
    + exact (to_interpret_poly_interpret_poly' P X).
    + exact (interpret_poly_to_interpret_poly P X).
Defined.

Definition to_interpret_poly_interpret_poly
           (P : poly_code)
           (X : UU)
           (x : ⟦ poly_container P ⟧ X)
  : to_interpret_poly P X (interpret_poly P X x) = x
  := homotinvweqweq (interpret_poly_weq P X) x.

(** W-types for containers *)
Inductive W (C : container) : UU :=
| sup : ⟦ C ⟧ (W C) → W C.

Fixpoint W_rec_map
         (C : container)
         (Y : UU)
         (fY : ⟦ C ⟧ Y → Y)
         (z : W C)
  : Y
  := match z with
     | sup _ f => fY (cpair
                        C
                        (pr1 f)
                        (λ p, W_rec_map C Y fY (pr2 f p)))
     end.

Definition W_rec_comp
           (C : container)
           (Y : UU)
           (fY : ⟦ C ⟧ Y → Y)
           (z : ⟦ C ⟧ (W C))
  : W_rec_map C Y fY (sup C z) = fY (interpret_map C (W_rec_map C Y fY) z)
  := idpath _.

Fixpoint W_ind_map
         (C : container)
         (Y : W C → UU)
         (Yc : ∏ (i : shapes C)
                 (f : positions C i → W C)
                 (v : ∏ (y : positions C i), Y(f y)),
               Y (sup C (i ,, f)))
         (z : W C)
  : Y z
  := match z with
     | sup _ z => Yc (pr1 z) (pr2 z) (λ i, W_ind_map C Y Yc (pr2 z i))
     end.

Definition W_ind_comp
           (C : container)
           (Y : W C → UU)
           (Yc : ∏ (i : shapes C)
                   (f : positions C i → W C)
                   (v : ∏ (y : positions C i), Y(f y)),
                 Y (sup C (i ,, f)))
           (z : ⟦ C ⟧ (W C))
  : W_ind_map C Y Yc (sup C z)
    =
    Yc (pr1 z) (pr2 z) (λ i, W_ind_map C Y Yc (pr2 z i))
  := idpath _.

(** W-types for polynomials *)
Definition poly_initial
           (P : poly_code)
  : UU
  := W (poly_container P).

Definition poly_initial_alg
           (P : poly_code)
  : poly_act P (poly_initial P) → poly_initial P
  := λ z, sup (poly_container P) (to_interpret_poly P _ z).

Definition poly_initial_rec
           (P : poly_code)
           (Y : UU)
           (fY : poly_act P Y → Y)
           (z : poly_initial P)
  : Y
  := W_rec_map
       (poly_container P) Y
       (λ q, fY (interpret_poly P Y q))
       z.

Definition poly_initial_comp_help
           (P : poly_code)
           (X Y : UU)
           (f : X → Y)
           (x : poly_act P X)
  : interpret_map
      (poly_container P)
      f
      (to_interpret_poly P X x)
    =
    to_interpret_poly P Y (poly_map P f x).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - use total2_paths_f.
    + apply idpath.
    + cbn.
      use funextsec.
      intro z ; induction z.
  - apply idpath.
  - induction x as [x | x].
    + use total2_paths_f.
      * exact (maponpaths inl (maponpaths pr1 (IHP₁ x))).
      * refine (_ @ fiber_paths (IHP₁ x)).
        use funextsec.
        intro z.
        refine (transportf_fun_space _ _ _ @ _ @ !(transportf_fun_space _ _ _)).
        apply maponpaths.
        refine (_ @ transportf_maponpaths_inl _ _ _ _).
        apply transportf_paths.
        refine (!_).
        exact (maponpathsinv0 inl _).
    + use total2_paths_f.
      * exact (maponpaths inr (maponpaths pr1 (IHP₂ x))).
      * refine (_ @ fiber_paths (IHP₂ x)).
        use funextsec.
        intro z.
        refine (transportf_fun_space _ _ _ @ _ @ !(transportf_fun_space _ _ _)).
        apply maponpaths.
        refine (_ @ transportf_maponpaths_inr _ _ _ _).
        apply transportf_paths.
        refine (!_).
        exact (maponpathsinv0 inr _).
  - use total2_paths_f.
    + exact (pathsdirprod
               (maponpaths pr1 (IHP₁ _))
               (maponpaths pr1 (IHP₂ _))).
    + use funextsec.
      intro z.
      refine (transportf_fun_space _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        simpl.
        apply transportb_maponpaths_pathsdirprod.
      }
      induction z as [z | z] ; simpl.
      * refine (_ @ eqtohomot (fiber_paths (IHP₁ _)) z).
        exact (!(transportf_fun_space _ _ _)).
      * refine (_ @ eqtohomot (fiber_paths (IHP₂ _)) z).
        exact (!(transportf_fun_space _ _ _)).
Defined.

Definition poly_initial_comp
           (P : poly_code)
           (Y : UU)
           (fY : poly_act P Y → Y)
           (z : poly_act P (poly_initial P))
  : poly_initial_rec
      P Y fY
      (poly_initial_alg P z)
    =
    fY (poly_map P (poly_initial_rec P Y fY) z).
Proof.
  refine (W_rec_comp
            (poly_container P) Y (λ q, fY (interpret_poly P Y q))
            _
          @
          maponpaths
            fY
            _).
  refine (_ @ interpret_poly_to_interpret_poly _ _ _).
  apply maponpaths.
  apply poly_initial_comp_help.
Defined.

Definition poly_initial_ind_help
           {P : poly_code}
           {T : UU}
           {Y : T → UU}
           {i : shapes (poly_container P)}
           {h : positions (poly_container P) i → T}
           (H : ∏ (y : positions (poly_container P) i), Y (h y))
  : poly_dact_UU P Y (interpret_poly P T (i,, h)).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact i.
  - exact (H tt).
  - induction i as [i | i].
    + exact (IHP₁ i h H).
    + exact (IHP₂ i h H).
  - exact (IHP₁ _ _ (λ z, H (inl z)) ,, IHP₂ _ _ (λ z, H (inr z))).
Defined.

Definition poly_initial_ind
           (P : poly_code)
           (Y : poly_initial P → UU)
           (Yc : ∏ (x : poly_act P (poly_initial P)),
                 poly_dact_UU P Y x
                 →
                 Y (poly_initial_alg P x))
  : ∏ (x : poly_initial P), Y x.
Proof.
  refine (W_ind_map
            (poly_container P)
            Y
            (λ i h H, _)).
  exact (transportf
           Y
           (maponpaths
              (sup _)
              (to_interpret_poly_interpret_poly _ _ _))
           (Yc (interpret_poly P _ (i ,, h)) (poly_initial_ind_help H))).
Defined.

Definition transportf_poly_dact_UU
           {P : poly_code}
           {X : UU}
           {Y : X → UU}
           (x : poly_act P X)
           (f : ∏ x : X, Y x)
  : transportf
      (poly_dact_UU P Y)
      (interpret_poly_to_interpret_poly P X x)
      (poly_initial_ind_help
         (λ i,
          f (pr2 (to_interpret_poly P X x) i)))
    =
    poly_dmap P Y f x.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (transportf_maponpaths_inl _ _ _ _ @ IHP₁ x).
    + exact (transportf_maponpaths_inr _ _ _ _ @ IHP₂ x).
  - exact (transportf_prod _ _ _ _
            @ pathsdirprod
                (IHP₁ (pr1 x))
                (IHP₂ (pr2 x))).
Qed.

Definition poly_initial_ind_comp_help
           {A B C : UU}
           {Y : A → UU}
           {Z : C → UU}
           {f : A → B} {f' : B → A}
           (e : ∏ a, f'(f a) = a)
           {g : B → C}
           (ff : ∏ (a : A), Y a → Z (g(f a)))
           {a : A}
           (y : Y (f' (f a)))
  : transportf
      Z
      (maponpaths g (maponpaths f (e a)))
      (ff (f'(f a)) y)
    =
    ff a (transportf Y (e a) y).
Proof.
  refine (_ @ transportf_depfun (λ z, g(f z)) ff (e a) y).
  apply transportf_paths.
  apply maponpathscomp.
Qed.
    
Definition poly_initial_ind_comp
           (P : poly_code)
           (Y : poly_initial P → UU)
           (Yc : ∏ (x : poly_act P (poly_initial P)),
                 poly_dact_UU P Y x
                 →
                 Y (poly_initial_alg P x))
           (x : poly_act P (poly_initial P))
  : poly_initial_ind P Y Yc (poly_initial_alg P x)
    =
    Yc x (poly_dmap P Y (poly_initial_ind P Y Yc) x).
Proof.
  cbn.
  etrans.
  {
    refine (maponpaths
              (λ z, transportf
                      Y
                      (maponpaths
                         (sup (poly_container P))
                         z)
                      _)
              _).
    refine (!(homotweqweqinvweq (interpret_poly_weq P (poly_initial P)) x) @ _).
    apply maponpaths.
    etrans.
    {
      apply pathscomp0rid.
    }
    apply pathsinv0inv0.
  }
  refine (poly_initial_ind_comp_help
            (interpret_poly_to_interpret_poly _ _)
            Yc
            _
          @ _).
  apply maponpaths.
  apply transportf_poly_dact_UU.
Qed.
