(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

(**
Data type of polynomials.
These are used for both the point constructor and the arguments of the path constructors.
 *)
Inductive poly_code : UU :=
| C : one_type → poly_code
| I : poly_code
| plus : poly_code → poly_code → poly_code
| times : poly_code → poly_code → poly_code.

Notation "P + Q" := (plus P Q).
Notation "P * Q" := (times P Q).

(** Action of polynomials on the universe *)
Definition poly_act
           (P : poly_code)
           (X : UU)
  : UU.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact A.
  - exact X.
  - exact (IHP₁ ⨿ IHP₂).
  - exact (IHP₁ × IHP₂).
Defined.

Definition poly_map
           (P : poly_code)
           {X Y : UU}
           (f : X → Y)
  : poly_act P X → poly_act P Y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ a, a).
  - exact f.
  - exact (coprodf IHP₁ IHP₂).
  - exact (dirprodf IHP₁ IHP₂).
Defined.

(**
Type of endpoints
 *)
Inductive endpoint (A : poly_code) : poly_code → poly_code → UU :=
(** endpoints for identity and composition *)
| id_e : ∏ (P : poly_code), endpoint A P P
| comp : ∏ (P Q R : poly_code), endpoint A P Q → endpoint A Q R → endpoint A P R
(** endpoints for sums *)
| ι₁ : ∏ (P Q : poly_code), endpoint A P (P + Q)
| ι₂ : ∏ (P Q : poly_code), endpoint A Q (P + Q)
(** endpoints for products *)
| π₁ : ∏ (P Q : poly_code), endpoint A (P * Q) P
| π₂ : ∏ (P Q : poly_code), endpoint A (P * Q) Q
| pair : ∏ (P Q R : poly_code),
    endpoint A P Q -> endpoint A P R → endpoint A P (Q * R)
(** endpoints for constant *)
| c : ∏ (P : poly_code) (T : one_type), T → endpoint A P (C T)
| fmap : ∏ {X Y : one_type} (f : X → Y), endpoint A (C X) (C Y)
(** constructor *)
| constr : endpoint A A I.

Arguments id {_} _.
Arguments comp {A} {P} {Q} {R} _ _.
Arguments ι₁ {_} P Q.
Arguments ι₂ {_} P Q.
Arguments π₁ {_} P Q.
Arguments π₂ {_} P Q.
Arguments pair {A} {P} {Q} {R} _ _.
Arguments c {_} P {_} _.
Arguments fmap {_} {X Y} f.
Arguments constr {_}.

(**
Endpoints induce functions
 *)
Definition sem_endpoint_UU
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : UU}
           (c : poly_act A X → X)
  : poly_act P X → poly_act Q X.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q
                  | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ f | ].
  - (* Identity *)
    exact (λ x, x).
  - (* Composition *)
    exact (λ x, IHe₂ (IHe₁ x)).
  - (* Left inclusion *)
    exact inl.
  - (* Right inclusion *)
    exact inr.
  - (* Left projection *)
    exact pr1.
  - (* Right projection *)
    exact pr2.
  - (* Pairing *)
    exact (λ x, IHe₁ x ,, IHe₂ x).
  - (* Constant *)
    exact (λ _, t).
  - (* Constant map *)
    exact f.
  - (* Constructor *)
    exact c.
Defined.

(**
Homotopy endpoints
Here:
- `A` is arguments of point constructor
- `J` is index for path constructors
- `S` is arguments for path constructors
- `l` and `r` are the left and right endpoint of the path constructors
- `Q` is the point argument
 *)
Inductive homot_endpoint
          {A : poly_code}
          {J : UU}
          {S : J → poly_code}
          (l : ∏ (j : J), endpoint A (S j) I)
          (r : ∏ (j : J), endpoint A (S j) I)
          {Q : poly_code}
          {TR : poly_code}
          (al ar : endpoint A Q TR)
  : ∏ {T : poly_code},
    endpoint A Q T → endpoint A Q T → UU
  :=
  (** operations on 2-cells *)
  | refl_e : ∏ (T : poly_code)
               (e : endpoint A Q T),
             homot_endpoint l r al ar e e
  | inv_e : ∏ (T : poly_code)
              (e₁ e₂ : endpoint A Q T),
            homot_endpoint l r al ar e₁ e₂
            →
            homot_endpoint l r al ar e₂ e₁
  | trans_e : ∏ (T : poly_code)
                (e₁ e₂ e₃ : endpoint A Q T),
              homot_endpoint l r al ar e₁ e₂
              →
              homot_endpoint l r al ar e₂ e₃
              →
              homot_endpoint l r al ar e₁ e₃
  | ap_e : ∏ (T₁ T₂ : poly_code)
             (e₁ e₂ : endpoint A Q T₁)
             (e₃ : endpoint A T₁ T₂),
           homot_endpoint
             l r al ar
             e₁ e₂
           →
           homot_endpoint
             l r al ar
             (comp e₁ e₃) (comp e₂ e₃)
  (** Associator and unitors *)
  | comp_assoc : ∏ (R₁ R₂ T : poly_code)
                   (e₁ : endpoint A Q R₁)
                   (e₂ : endpoint A R₁ R₂)
                   (e₃ : endpoint A R₂ T),
                 homot_endpoint
                   l r al ar
                   (comp e₁ (comp e₂ e₃))
                   (comp (comp e₁ e₂) e₃)
  | comp_id_l : ∏ (T : poly_code)
                  (e : endpoint A Q T),
                homot_endpoint
                  l r al ar
                  (comp (id_e _ _) e)
                  e
  | comp_id_r : ∏ (T : poly_code)
                  (e : endpoint A Q T),
                homot_endpoint
                  l r al ar
                  (comp e (id_e _ _))
                  e
  (** Beta rules for product *)
  | pair_π₁ : ∏ (P R : poly_code)
                (e₁ : endpoint A Q P)
                (e₂ : endpoint A Q R),
              homot_endpoint
                l r al ar
                (comp (pair e₁ e₂) (π₁ _ _))
                e₁
  | pair_π₂ : ∏ (P R : poly_code)
                (e₁ : endpoint A Q P)
                (e₂ : endpoint A Q R),
              homot_endpoint
                l r al ar
                (comp (pair e₁ e₂) (π₂ _ _))
                e₂
  | path_pair : ∏ (T₁ T₂ : poly_code)
                  (e₁ e₂ : endpoint A Q T₁)
                  (e₃ e₄ : endpoint A Q T₂),
                homot_endpoint l r al ar e₁ e₂
                →
                homot_endpoint l r al ar e₃ e₄
                →
                homot_endpoint
                  l r al ar
                  (pair e₁ e₃) (pair e₂ e₄)
  (** In categories, this one follows from uniqueness *) 
  | comp_pair : ∏ {P₁ P₂ P₃ : poly_code}
                  (e₁ : endpoint A Q P₁)
                  (e₂ : endpoint A P₁ P₂)
                  (e₃ : endpoint A P₁ P₃),
                homot_endpoint
                  l r
                  al ar
                  (comp e₁ (pair e₂ e₃))
                  (pair (comp e₁ e₂) (comp e₁ e₃))
  (** Rules for constant *)
  | comp_constant : ∏ (X : one_type)
                      (x : X)
                      (T : poly_code)
                      (e : endpoint A Q T),
                    homot_endpoint
                      l r al ar
                      (comp e (c T x)) (c Q x)
  (** Path constructor and path argument *)                
  | path_constr : ∏ (j : J)
                    (e : endpoint A Q (S j)),
                  homot_endpoint
                    l r al ar
                    (comp e (l j))
                    (comp e (r j))
  | path_arg : homot_endpoint
                 l r
                 al ar
                 al ar.

Arguments refl_e {_ _ _ _ _ _ _ _ _ _}.
Arguments inv_e {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments trans_e {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments ap_e {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments comp_assoc {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments comp_id_l {_ _ _ _ _ _ _ _ _ _} _.
Arguments comp_id_r {_ _ _ _ _ _ _ _ _ _} _.
Arguments pair_π₁ {_ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments pair_π₂ {_ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments path_pair {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments comp_pair {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments comp_constant {_ _ _ _ _ _ _ _ _ _} _ {_} _.
Arguments path_constr {_ _ _ _ _ _ _ _ _} _ _.
Arguments path_arg {_ _ _ _ _ _ _ _ _}.

Section MoreHomotopyEndpoints.
  Context {A : poly_code}
          {J : UU}
          {S : J → poly_code}
          {l : ∏ (j : J), endpoint A (S j) I}
          {r : ∏ (j : J), endpoint A (S j) I}
          {Q : poly_code}
          {TR : poly_code}
          {al ar : endpoint A Q TR}.

  Definition path_pr1
             {T₁ T₂ : poly_code}
             {e₁ e₂ : endpoint A Q T₁}
             {e₃ e₄ : endpoint A Q T₂}
             (h : homot_endpoint
                    l r al ar
                    (pair e₁ e₃) (pair e₂ e₄))
    : homot_endpoint l r al ar e₁ e₂
    := trans_e
         (trans_e
            (inv_e (pair_π₁ _ _))
            (ap_e (π₁ _ _) h))
         (pair_π₁ _ _).

  Definition path_pr2
             {T₁ T₂ : poly_code}
             {e₁ e₂ : endpoint A Q T₁}
             {e₃ e₄ : endpoint A Q T₂}
             (h : homot_endpoint
                    l r al ar
                    (pair e₁ e₃) (pair e₂ e₄))
    : homot_endpoint l r al ar e₃ e₄
    := trans_e
         (trans_e
            (inv_e (pair_π₂ _ _))
            (ap_e (π₂ _ _) h))
         (pair_π₂ _ _).

  Definition path_inl
             (T₁ T₂ : poly_code)
             (e₁ e₂ : endpoint A Q T₁)
             (h : homot_endpoint l r al ar e₁ e₂)
    : homot_endpoint
        l r al ar
        (comp e₁ (ι₁ _ _))
        (comp e₂ (ι₁ _ T₂))
    := ap_e (ι₁ _ _) h.

  Definition path_inr
             (T₁ T₂ : poly_code)
             (e₁ e₂ : endpoint A Q T₁)
             (h : homot_endpoint l r al ar e₁ e₂)
    : homot_endpoint
        l r al ar
        (comp e₁ (ι₂ _ _))
        (comp e₂ (ι₂ T₁ _))
    := ap_e (ι₂ _ _) h.
End MoreHomotopyEndpoints.

(**
The definition of a HIT signature
The shape is:
HIT H :=
| c : A H → H
| p : ∏ (j : J₁) (x : S₁ j H), l j x = r j x
| s : ∏ (j : J₂) (x : Q j H) (p : sl j = sr j), s₁ j p x = s₂ j p x
where we have    s₁ j p x, s₂ j p x : sl j x = sr j x
 *)
Definition hit_signature
  : UU
  := ∑ (A : poly_code),
     ∑ (J₁ : Type),
     ∑ (S : J₁ → poly_code),
     ∑ (l r : ∏ (j : J₁), endpoint A (S j) I),
     ∑ (J₂ : Type),
     ∑ (Q : J₂ → poly_code),
     ∑ (TR : J₂ → poly_code),
     ∑ (sl sr : ∏ (j : J₂), endpoint A (Q j) (TR j)),
     ∑ (psl psr : ∏ (j : J₂), endpoint A (Q j) I),
     (∏ (j : J₂),
      homot_endpoint
        l r
        (sl j) (sr j)
        (psl j) (psr j))
     ×
     (∏ (j : J₂),
      homot_endpoint
        l r
        (sl j) (sr j)
        (psl j) (psr j)).

(** Projections of HIT signature *)
Section Projections.
  Variable (Σ : hit_signature).
  
  Definition point_constr
    : poly_code
    := pr1 Σ.

  Definition path_label
    : Type
    := pr12 Σ.

  Definition path_source
    : path_label → poly_code
    := pr122 Σ.

  Definition path_left
    : ∏ (j : path_label), endpoint point_constr (path_source j) I
    := pr1 (pr222 Σ).

  Definition path_right
    : ∏ (j : path_label), endpoint point_constr (path_source j) I
    := pr12 (pr222 Σ).

  Definition homot_label
    : Type
    := pr122 (pr222 Σ).

  Definition homot_point_arg
    : homot_label → poly_code
    := pr1 (pr222 (pr222 Σ)).

  Definition homot_path_arg_target
    : homot_label → poly_code
    := pr12 (pr222 (pr222 Σ)).

  Definition homot_path_arg_left
    : ∏ (j : homot_label),
      endpoint
        point_constr
        (homot_point_arg j)
        (homot_path_arg_target j)
    := pr122 (pr222 (pr222 Σ)).

  Definition homot_path_arg_right
    : ∏ (j : homot_label),
      endpoint
        point_constr
        (homot_point_arg j)
        (homot_path_arg_target j)
    := pr1 (pr222 (pr222 (pr222 Σ))).

  Definition homot_left_endpoint
    : ∏ (j : homot_label),
      endpoint
        point_constr
        (homot_point_arg j)
        I
    := pr12 (pr222 (pr222 (pr222 Σ))).

  Definition homot_right_endpoint
    : ∏ (j : homot_label),
      endpoint
        point_constr
        (homot_point_arg j)
        I
    := pr122 (pr222 (pr222 (pr222 Σ))).

  Definition homot_left_path
    : ∏ (j : homot_label),
      homot_endpoint
        path_left path_right
        (homot_path_arg_left j)
        (homot_path_arg_right j)
        (homot_left_endpoint j)
        (homot_right_endpoint j)
    := pr1 (pr222 (pr222 (pr222 (pr222 Σ)))).

  Definition homot_right_path
    : ∏ (j : homot_label),
      homot_endpoint
        path_left path_right
        (homot_path_arg_left j)
        (homot_path_arg_right j)
        (homot_left_endpoint j)
        (homot_right_endpoint j)
    := pr2 (pr222 (pr222 (pr222 (pr222 Σ)))).
End Projections.

Definition sem_homot_endpoint_UU
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l : ∏ (j : J), endpoint A (S j) I}
           {r : ∏ (j : J), endpoint A (S j) I}
           {Q : poly_code}
           {TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : poly_code}
           {sl sr : endpoint A Q T}
           (p : homot_endpoint l r al ar sl sr)
           (X : UU)
           (c : poly_act A X → X)
           (pX : ∏ (i : J),
                 sem_endpoint_UU (l i) c
                 ~
                 sem_endpoint_UU (r i) c)
           (z : poly_act Q X)
           (p_arg : sem_endpoint_UU al c z = sem_endpoint_UU ar c z)
  : sem_endpoint_UU sl c z = sem_endpoint_UU sr c z.
Proof.
  induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | T₁ T₂ e₁ e₂ e₃ h IHh
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | P R e₁ e₂ | P R e₁ e₂
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | P₁ P₂ P₃ e₁ e₂ e₃
                  | Z x T e | j e | ].
  - (** identity path *)
    exact (idpath _).
  - (** inverse path *)
    exact (!IHp).
  - (** concatenation of paths *)
    exact (IHP₁ @ IHP₂).
  - (** ap on paths *)
    exact (maponpaths (sem_endpoint_UU e₃ c) IHh).
  - (** associator *)
    apply idpath.
  - (** left unitor *)
    apply idpath.
  - (** right unitor *)
    apply idpath.
  - (** first projection *)
    apply idpath.
  - (** second projection *)
    apply idpath.
  - (** pairing *)
    exact (pathsdirprod IHp₁ IHp₂).
  - (** composition before pair *)
    apply idpath.
  - (** composition with constant *)
    apply idpath.
  - (** path constructor *)
    exact (pX j _).
  - (** path argument *)
    exact p_arg.
Defined.
