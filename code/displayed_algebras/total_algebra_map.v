Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import prelude.all.

Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.

Local Open Scope cat.

Local Definition TODO {A : UU} : A.
Admitted.

(*
(** We first show operations of displayed algebras commute with transports *)
Definition transportb_disp_alg_operator
           {P : poly_code}
           {A : one_type}
           (Y : A → one_type)
           (c : poly_act P A → A)
           (cY : ∏ (x : poly_act P A), poly_dact P Y x → Y (c x))
           {a₁ a₂ : poly_act P A}
           (p : a₁ = a₂)
           (y : poly_dact P Y a₁)
  : cY a₁ y
    =
    transportb Y (maponpaths c p) (cY a₂ (transportf (poly_dact P Y) p y)).
Proof.
  induction p.
  apply idpath.
Qed.

(** Next we compute `poly_pr2` composed with the action of the functor *)
Definition poly_pr2_fmap
           (P : poly_code)
           {X : one_type}
           (Y : X → one_type)
           (f : X → total2_one_type Y)
           (x : poly_act P X)
           (p : (λ z, pr1(f z)) = idfun X)
  : poly_pr2 P (poly_map P f x)
    =
    transportf
      (poly_dact P Y)
      (eqtohomot (!(functor_id _ _)) x
                 @ eqtohomot (maponpaths (poly_map P) (!p)) x
                 @ eqtohomot (functor_comp _ _ _) x)
      (poly_dmap P Y (λ z, transportf Y (eqtohomot p z) (pr2 (f z))) x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl.
  - rewrite transportf_const.
    reflexivity.
  - rewrite transport_f_f.
    rewrite transportf_set.
    + reflexivity.
    + apply X.
  - induction x as [x | x].
    + refine (IHP₁ x @ _).
      refine (!(transportf_inl (poly_dact P₁ Y) (poly_dact P₂ Y) _ _) @ _).
      apply (transportf_paths (sum_hset_fam (poly_dact P₁ Y) (poly_dact P₂ Y))).
      apply setcoprod.
    + refine (IHP₂ x @ _).
      refine (!(transportf_inr (poly_dact P₁ Y) (poly_dact P₂ Y) _ _) @ _).
      apply (transportf_paths (sum_hset_fam (poly_dact P₁ Y) (poly_dact P₂ Y))).
      apply setcoprod.
  - induction x as [x₁ x₂].
    apply dirprod_paths.
    + refine (IHP₁ x₁ @ _).
      refine (_ @ !(transportf_pr1 _ (#⦃ P₁ ⦄ _ _ ,, #⦃ P₂ ⦄ _ _) _ _)).
      apply (transportf_paths (poly_dact P₁ Y)).
      apply setproperty.
    + refine (IHP₂ x₂ @ _).
      refine (_ @ !(transportf_pr2 _ (#⦃ P₁ ⦄ _ _ ,, #⦃ P₂ ⦄ _ _) _ _)).
      apply (transportf_paths (poly_dact P₂ Y)).
      apply setproperty.
Qed.
*)

(** Lemma *)
(*
Definition functor_fid
           {P : poly_code}
           {X : hSet}
           {x : ⦃ P ⦄ X}
           {f : X → X}
           (p : f = idfun X)
  : x = #⦃ P ⦄ f x.
Proof.
  rewrite p.
  rewrite (functor_id (⦃ P ⦄)).
  reflexivity.
Qed.
 *)

Local Arguments PathOver {_ _ _} _ _ _ _.

Definition transport_depmap
           {A : UU}
           {Y : A → UU}
           {f : A → A}
           (ff : ∏ (x : A), Y(f x))
           (p : f = λ a, a)
  : ∏ (a : A), Y a
  := λ a, transportf Y (eqtohomot p a) (ff a).

Definition test
           {A : UU}
           {Y : A → UU}
           {f : A → A}
           (p : f = λ a, a)
           {a₁ a₂ : A}
           {q : a₁ = a₂}
           {y₁ : Y(f a₁)} {y₂ : Y(f a₂)}
           (pp : PathOver (λ a, Y(f a)) y₁ y₂ q)
  : PathOver
      Y
      (transportf Y (eqtohomot p a₁) y₁)
      (transportf Y (eqtohomot p a₂) y₂)
      q.
Proof.
  induction q.
  simpl in * ; unfold transport_depmap.
  apply maponpaths.
  exact pp.
Defined.

Definition apd_transport_depmap
           {A : UU}
           {Y : A → UU}
           {f : A → A}
           (ff : ∏ (x : A), Y(f x))
           (p : f = λ a, a)
           {a₁ a₂ : A}
           (q : a₁ = a₂)
  : PathOver_square
      Y
      (idpath _)
      (apd (transport_depmap ff p) q)
      (test p (apd ff q))
      (idpath _)
      (idpath _).
Proof.
  induction q.
  simpl.
  apply idpath.
Qed.

Definition test2
           {A : UU}
           {Y : A → UU}
           (f : A → ∑ (x : A), Y x)
           (e : (λ a, pr1 (f a)) = λ a, a)
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           (s : PathOver
                  Y
                  (pr2 (f a₁))
                  (pr2 (f a₂))
                  (maponpaths pr1 (maponpaths f p)))
  : PathOver
      Y
      (transportf Y (eqtohomot e a₁) (pr2 (f a₁)))
      (transportf Y (eqtohomot e a₂) (pr2 (f a₂)))
      p.
Proof.
  induction p.
  simpl in *.
  apply maponpaths.
  exact s.
Defined.

Definition maponpaths_eq
           {A B : UU}
           {f g : A → B}
           (e : f = g)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : !(eqtohomot e a₁)
    @ maponpaths f p
    @ eqtohomot e a₂
    =
    maponpaths g p.
Proof.
  induction e.
  simpl.
  apply pathscomp0rid.
Defined.

Definition ap_sigma_to_apd_help
           {A : UU}
           {Y : A → UU}
           (f : A → ∑ (x : A), Y x)
           (e : (λ a, pr1 (f a)) = λ a, a)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : p = !(eqtohomot e a₁) @ maponpaths pr1 (maponpaths f p) @ eqtohomot e a₂.
Proof.
  refine (!(maponpathsidfun _) @ !(maponpaths_eq e p) @ _).
  apply maponpaths.
  apply maponpaths_2.
  refine (!_).
  apply maponpathscomp.
Defined.

Definition PathOver_transport
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (y : Y a₁)
  : PathOver Y y (transportf Y p y) p.
Proof.
  induction p.
  apply idpath.
Defined.

Definition ap_sigma_to_apd
           {A : UU}
           {Y : A → UU}
           (f : A → ∑ (x : A), Y x)
           (e : (λ a, pr1 (f a)) = λ a, a)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : PathOver_square
      Y
      (ap_sigma_to_apd_help f e p)
      (test
         e
         (apd (λ z, pr2 (f z)) p))
      (composePathOver
         (inversePathOver (PathOver_transport _ _))
         (composePathOver
            (TotalPathToPathOver (maponpaths f p))
            (PathOver_transport _ _)))
      (idpath _)
      (idpath _).
Proof.
  induction p.
  apply TODO.
Qed.
  

Definition PathOver_square_concat
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ p₃ : a₁ = a₂}
           {h₁ : p₁ = p₂} {h₂ : p₂ = p₃}
           {x₁ y₁ z₁ : Y a₁}
           {x₂ y₂ z₂ : Y a₂}
           {pp₁ : PathOver Y x₁ x₂ p₁}
           {pp₂ : PathOver Y y₁ y₂ p₂}
           {pp₃ : PathOver Y z₁ z₂ p₃}
           {q₁ : x₁ = y₁} {q₂ : x₂ = y₂}
           {r₁ : y₁ = z₁} {r₂ : y₂ = z₂}
           (s₁ : PathOver_square Y h₁ pp₁ pp₂ q₁ q₂)
           (s₂ : PathOver_square Y h₂ pp₂ pp₃ r₁ r₂)
  : PathOver_square
      Y
      (h₁ @ h₂)
      pp₁ pp₃
      (q₁ @ r₁) (q₂ @ r₂).
Proof.
  induction q₁, q₂, h₁, h₂, s₁.
  exact s₂.
Qed.

Definition transporf_to_right
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : X}
           {p : x₁ = x₂}
           {y₁ : Y x₁} {y₂ : Y x₂}
  : transportf Y p y₁ = y₂ → y₁ = transportb Y p y₂.
Proof.
  induction p ; cbn.
  exact (λ p, p).
Defined.

Definition lol
           {A : UU}
           {Y : A → UU}
           (f : A → ∑ (x : A), Y x)
           (e : (λ a, pr1 (f a)) = λ a, a)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : maponpaths pr1 (maponpaths f p) = eqtohomot e a₁ @ p @ !(eqtohomot e a₂).
Proof.
  apply TODO.
Defined.

Definition PathOver_square_1_type
           {A : one_type}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h₁ h₂ : p₁ = p₂}
           {x₁ y₁ : Y a₁}
           {x₂ y₂ : Y a₂}
           {pp₁ : PathOver Y x₁ x₂ p₁}
           {pp₂ : PathOver Y y₁ y₂ p₂}
           {q₁ : x₁ = y₁} {q₂ : x₂ = y₂}
           (s : PathOver_square Y h₁ pp₁ pp₂ q₁ q₂)
  : PathOver_square Y h₂ pp₁ pp₂ q₁ q₂.
Proof.
  assert (h₁ = h₂) as X.
  {
    apply (one_type_isofhlevel A).
  }
  induction X.
  exact s.
Qed.


Definition PathTotalPathToPathOver
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (z : X), Y z}
           {p q : x = y}
           (h : p = q)
  : PathOver_square
      Y
      (maponpaths (maponpaths pr1) h)
      (TotalPathToPathOver p)
      (TotalPathToPathOver q)
      (idpath _)
      (idpath _).
Proof.
  induction h.
  apply idpath.
Qed.

Definition TotalPathToPathOver_concat
           {X : UU}
           {Y : X → UU}
           {x y z : ∑ (z : X), Y z}
           (p : x = y) (q : y = z)
  : PathOver_square
      Y
      (maponpathscomp0 pr1 p q)
      (TotalPathToPathOver (p @ q))
      (composePathOver
         (TotalPathToPathOver p)
         (TotalPathToPathOver q))
      (idpath _)
      (idpath _).
Proof.
  induction p, q.
  apply idpath.
Qed.

Definition TotalPathToPathOver_inv
           {X : UU}
           {Y : X → UU}
           {x y : ∑ (z : X), Y z}
           (p : x = y)
  : PathOver_square
      Y
      (maponpathsinv0 pr1 p)
      (TotalPathToPathOver (!p))
      (inversePathOver (TotalPathToPathOver p))
      (idpath _)
      (idpath _).
Proof.
  induction p.
  apply idpath.
Qed.

Definition PathOver_square_comp_l
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ a₃ : A}
           {p₁ : a₁ = a₂} {p₂ p₃ : a₂ = a₃}
           {h : p₂ = p₃}
           {x₁ : Y a₁}
           {x₂ : Y a₂}
           {x₃ : Y a₃}
           {pp : PathOver Y x₂ x₃ p₂}
           {qq : PathOver Y x₂ x₃ p₃}
           (rr : PathOver Y x₁ x₂ p₁)
           (s : PathOver_square Y h pp qq (idpath _) (idpath _))
  : PathOver_square
      Y
      (maponpaths (λ z, p₁ @ z) h)
      (composePathOver rr pp)
      (composePathOver rr qq)
      (idpath _)
      (idpath _).
Proof.
  induction h, p₁, p₂, s.
  apply idpath.
Qed.


Definition PathOver_square_comp_r
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ a₃ : A}
           {p₁ p₂ : a₁ = a₂} {p₃ : a₂ = a₃}
           {h : p₁ = p₂}
           {x₁ : Y a₁}
           {x₂ : Y a₂}
           {x₃ : Y a₃}
           {pp : PathOver Y x₁ x₂ p₁}
           {qq : PathOver Y x₁ x₂ p₂}
           (rr : PathOver Y x₂ x₃ p₃)
           (s : PathOver_square Y h pp qq (idpath _) (idpath _))
  : PathOver_square
      Y
      (maponpaths (λ z, z @ p₃) h)
      (composePathOver pp rr)
      (composePathOver qq rr)
      (idpath _)
      (idpath _).
Proof.
  induction h, p₁, p₃, s.
  apply idpath.
Qed.

Definition composePathOver_assocl
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄}
           {x₁ : Y a₁} {x₂ : Y a₂} {x₃ : Y a₃} {x₄ : Y a₄}
           (pp : PathOver Y x₁ x₂ p₁)
           (qq : PathOver Y x₂ x₃ p₂)
           (rr : PathOver Y x₃ x₄ p₃)
  : PathOver_square
      Y
      (path_assoc _ _ _)
      (composePathOver pp (composePathOver qq rr))
      (composePathOver (composePathOver pp qq) rr)
      (idpath _)
      (idpath _).
Proof.
  induction p₁, p₂, p₃.
  apply path_assoc.
Qed.

Definition composePathOver_assocr
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ a₃ a₄ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄}
           {x₁ : Y a₁} {x₂ : Y a₂} {x₃ : Y a₃} {x₄ : Y a₄}
           (pp : PathOver Y x₁ x₂ p₁)
           (qq : PathOver Y x₂ x₃ p₂)
           (rr : PathOver Y x₃ x₄ p₃)
  : PathOver_square
      Y
      (!(path_assoc _ _ _))
      (composePathOver (composePathOver pp qq) rr)
      (composePathOver pp (composePathOver qq rr))
      (idpath _)
      (idpath _).
Proof.
  induction p₁, p₂, p₃.
  exact (!(path_assoc _ _ _)).
Qed.

Definition TotalPathToPathOver_PathOverToTotalPath
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {y₁ : Y a₁} {y₂ : Y a₂}
           {p : a₁ = a₂}
           (pp : PathOver Y y₁ y₂ p)
  : PathOver_square
      Y
      (maponpaths_pr1_PathOverToTotalPath p pp)
      (TotalPathToPathOver (PathOverToTotalPath pp))
      pp
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

(** Now we show that a section of the projection gives rise to a dependent map to `Y` *)
Section SectionToDispAlgMap.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}
          (Y : disp_algebra X)
          (f : X --> total_algebra Y)
          (p : f · projection Y = identity X).

  Local Notation "'p_path'" := (maponpaths (λ f, pr111 f) p).

  Definition section_to_disp_alg_map_comp
    : ∏ x : alg_carrier X, Y x
    := transport_depmap
         (λ z, pr2 (pr111 f z))
         p_path.

  Definition section_to_disp_alg_map_constr
             (x : poly_act (point_constr Σ) (alg_carrier X))
    : section_to_disp_alg_map_comp (alg_constr X x) =
      disp_alg_constr
        Y x
        (poly_dmap
           (point_constr Σ)
           Y
           section_to_disp_alg_map_comp
           x).
  Proof.
    etrans.
    {
      refine (maponpaths
                (transportf Y (eqtohomot p_path (alg_constr X x)))
                _).
      pose (transporf_to_right (fiber_paths (pr1 (pr211 f) x))) as p0.
      simpl in p0 ; cbn in p0.
      exact p0.
    }
    etrans.
    {
      apply transport_f_b.
    }
    apply TODO.
  Defined.

  Section Apd.
    Variable (j : path_label Σ)
             (x : poly_act (path_source Σ j) (alg_carrier X)).

    Definition apd_section_to_disp_alg_map₁
      : PathOver_square
          Y
          (idpath _)
          (apd section_to_disp_alg_map_comp (alg_path X j x))
          (test p_path (apd (λ z, pr2 ((pr111 f) z)) (alg_path X j x)))
          (idpath _)
          (idpath _).
    Proof.
      exact (apd_transport_depmap
               (λ z, pr2 ((pr111 f) z))
               (maponpaths (λ f, pr111 f) p)
               (alg_path X j x)).
    Qed.

    Definition apd_section_to_disp_alg_map₂
      : PathOver_square
          Y
          (ap_sigma_to_apd_help (pr111 f) p_path (alg_path X j x))
          (test p_path (apd (λ z, pr2 ((pr111 f) z)) (alg_path X j x)))
          (composePathOver
             (inversePathOver
                (PathOver_transport
                   (eqtohomot p_path (sem_endpoint_one_types (path_left Σ j) (pr11 X) x))
                   (pr2 ((pr111 f) (sem_endpoint_one_types (path_left Σ j) (pr11 X) x)))))
             (composePathOver
                (TotalPathToPathOver (maponpaths (pr111 f) (alg_path X j x)))
                (PathOver_transport
                   (eqtohomot p_path (sem_endpoint_one_types (path_right Σ j) (pr11 X) x))
                   (pr2 ((pr111 f) (sem_endpoint_one_types (path_right Σ j) (pr11 X) x))))))
          (idpath _)
          (idpath _).
    Proof.
      exact (ap_sigma_to_apd _ p_path (alg_path X j x)).
    Qed.

    Definition apd_section_to_disp_alg_map₃_help_path
      : maponpaths (pr111 f) ((pr21 X) j x)
        =
        sem_endpoint_UU_natural (path_left Σ j) (pr121 (pr1 f)) x
        @ total_algebra.paths Y j (poly_map (path_source Σ j) (pr111 f) x)
        @ !(sem_endpoint_UU_natural (path_right Σ j) (pr121 (pr1 f)) x).
    Proof.
      refine (_ @ !(path_assoc _ _ _)).
      use path_inv_rotate_rr.
      exact (eqtohomot (pr21 f j) x).
    Qed.

    Definition apd_section_to_disp_alg_map₃_index
      : maponpaths pr1 (maponpaths (pr111 f) ((pr21 X) j x))
        =
        maponpaths
          pr1
          (sem_endpoint_UU_natural (path_left Σ j) (pr121 (pr1 f)) x)
        @ maponpaths
            pr1
            (total_algebra.paths Y j (poly_map (path_source Σ j) (pr111 f) x))
        @ !(maponpaths
              pr1
              (sem_endpoint_UU_natural (path_right Σ j) (pr121 (pr1 f)) x)).
    Proof.
      exact
        (maponpaths (maponpaths pr1) apd_section_to_disp_alg_map₃_help_path
         @ maponpathscomp0 pr1 _ _
         @ maponpaths
             _
             (maponpathscomp0 pr1 _ _
              @ maponpaths
                  _
                  (maponpathsinv0 _ _))).
    Qed.

    Definition apd_section_to_disp_alg_map₃_help
      : PathOver_square
          Y
          apd_section_to_disp_alg_map₃_index
          (TotalPathToPathOver (maponpaths (pr111 f) ((pr21 X) j x)))
          (composePathOver
             (TotalPathToPathOver
                (sem_endpoint_UU_natural (path_left Σ j) (pr121 (pr1 f)) x))
             (composePathOver
                (TotalPathToPathOver
                   (total_algebra.paths Y j (poly_map (path_source Σ j) (pr111 f) x)))
                (inversePathOver
                   (TotalPathToPathOver
                      (sem_endpoint_UU_natural (path_right Σ j) (pr121 (pr1 f)) x)))))
          (idpath  _)
          (idpath  _).
    Proof.
      refine
        (PathOver_square_1_type
           (PathOver_square_concat
              (PathTotalPathToPathOver apd_section_to_disp_alg_map₃_help_path)
              (PathOver_square_concat
                 (TotalPathToPathOver_concat _ _)
                 (PathOver_square_comp_l
                    _
                    (PathOver_square_1_type
                       (PathOver_square_concat
                          (TotalPathToPathOver_concat _ _)
                          (PathOver_square_comp_l
                             _
                             (PathOver_square_1_type
                                (TotalPathToPathOver_inv _))))))))).
      - etrans.
        {
          apply (maponpathscomp0 pr1).
        }
        apply maponpaths.
        apply maponpathsinv0.
      - apply maponpathsinv0.
    Qed.

    Definition apd_section_to_disp_alg_map₃
      : PathOver_square
          Y
          (maponpaths
             (λ z, _ @ z)
             (maponpaths (λ z, z @ _) apd_section_to_disp_alg_map₃_index))
          (composePathOver
             (inversePathOver
                (PathOver_transport
                   (eqtohomot p_path (sem_endpoint_one_types (path_left Σ j) (pr11 X) x))
                   (pr2 ((pr111 f) (sem_endpoint_one_types (path_left Σ j) (pr11 X) x)))))
             (composePathOver
                (TotalPathToPathOver (maponpaths (pr111 f) ((pr21 X) j x)))
                (PathOver_transport
                   (eqtohomot p_path (sem_endpoint_one_types (path_right Σ j) (pr11 X) x))
                   (pr2 ((pr111 f) (sem_endpoint_one_types (path_right Σ j) (pr11 X) x))))))
          (composePathOver
             (inversePathOver
                (PathOver_transport
                   (eqtohomot p_path (sem_endpoint_one_types (path_left Σ j) (pr11 X) x))
                   (pr2 ((pr111 f) (sem_endpoint_one_types (path_left Σ j) (pr11 X) x)))))
             (composePathOver
                (composePathOver
                   (TotalPathToPathOver
                      (sem_endpoint_UU_natural (path_left Σ j) (pr121 (pr1 f)) x))
                   (composePathOver
                      (TotalPathToPathOver
                         (total_algebra.paths Y j (poly_map (path_source Σ j) (pr111 f) x)))
                      (inversePathOver
                         (TotalPathToPathOver
                            (sem_endpoint_UU_natural (path_right Σ j) (pr121 (pr1 f)) x)))))
                (PathOver_transport
                   (eqtohomot p_path (sem_endpoint_one_types (path_right Σ j) (pr11 X) x))
                   (pr2 ((pr111 f) (sem_endpoint_one_types (path_right Σ j) (pr11 X) x))))))
          (idpath _)
          (idpath _).
    Proof.
      exact (PathOver_square_comp_l
               (inversePathOver
                  (PathOver_transport
                     (eqtohomot p_path _)
                     _))
               (PathOver_square_comp_r
                  (PathOver_transport
                     (eqtohomot p_path _)
                     _)
                  apd_section_to_disp_alg_map₃_help)).
    Qed.

    Definition apd_section_to_disp_alg_map₄_left
      := composePathOver
           (composePathOver
              (inversePathOver
                 (PathOver_transport
                    (eqtohomot p_path _)
                    (pr2 ((pr111 f) _))))
              (TotalPathToPathOver
                 (sem_endpoint_UU_natural (path_left Σ j) (pr121 (pr1 f)) x)))
           (inversePathOver
              (total_algebra.pr2_endpoint
                 Y (path_left Σ j)
                 (poly_map (path_source Σ j) (pr111 f) x))).

    Definition apd_section_to_disp_alg_map₄_right
      := composePathOver
           (total_algebra.pr2_endpoint
              Y (path_right Σ j)
              (poly_map (path_source Σ j) (pr111 f) x))
           (composePathOver
              (inversePathOver
                 (TotalPathToPathOver
                    (sem_endpoint_UU_natural (path_right Σ j) (pr121 (pr1 f)) x)))
              (PathOver_transport
                 (eqtohomot p_path _)
                 (pr2 ((pr111 f) _)))).
    
    Definition apd_section_to_disp_alg_map₄
      : PathOver_square
          Y
          TODO
          (composePathOver
             (inversePathOver
                (PathOver_transport
                   (eqtohomot p_path (sem_endpoint_one_types (path_left Σ j) (pr11 X) x))
                   (pr2 ((pr111 f) (sem_endpoint_one_types (path_left Σ j) (pr11 X) x)))))
             (composePathOver
                (composePathOver
                   (TotalPathToPathOver
                      (sem_endpoint_UU_natural (path_left Σ j) (pr121 (pr1 f)) x))
                   (composePathOver
                      (TotalPathToPathOver
                         (total_algebra.paths Y j (poly_map (path_source Σ j) (pr111 f) x)))
                      (inversePathOver
                         (TotalPathToPathOver
                            (sem_endpoint_UU_natural (path_right Σ j) (pr121 (pr1 f)) x)))))
                (PathOver_transport
                   (eqtohomot p_path (sem_endpoint_one_types (path_right Σ j) (pr11 X) x))
                   (pr2 ((pr111 f) (sem_endpoint_one_types (path_right Σ j) (pr11 X) x))))))
          (composePathOver
             apd_section_to_disp_alg_map₄_left
             (composePathOver
                (disp_alg_path
                   Y j
                   (poly_pr1 _ (poly_map (path_source Σ j) (pr111 f) x))
                   (poly_pr2 _ (poly_map (path_source Σ j) (pr111 f) x)))
                apd_section_to_disp_alg_map₄_right))
          (idpath  _)
          (idpath  _).
    Proof.
      apply TODO.
    Qed.

    Definition apd_section_to_disp_alg_map₅
      : PathOver_square
          Y
          TODO
          (composePathOver
             apd_section_to_disp_alg_map₄_left
             (composePathOver
                (disp_alg_path
                   Y j
                   (poly_pr1 _ (poly_map (path_source Σ j) (pr111 f) x))
                   (poly_pr2 _ (poly_map (path_source Σ j) (pr111 f) x)))
                apd_section_to_disp_alg_map₄_right))
          (disp_alg_path
             Y j x
             (poly_dmap
                (path_source Σ j)
                Y
                section_to_disp_alg_map_comp x))
          (endpoint_dact_natural (path_left Σ j) section_to_disp_alg_map_constr x)
          (endpoint_dact_natural (path_right Σ j) section_to_disp_alg_map_constr x).
    Proof.
      apply TODO.
    Qed.
    
    Definition apd_section_to_disp_alg_map
      : PathOver_square
          Y
          (idpath _)
          (apd section_to_disp_alg_map_comp (alg_path X j x))
          (disp_alg_path
             Y j x
             (poly_dmap
                (path_source Σ j)
                Y
                section_to_disp_alg_map_comp x))
          (endpoint_dact_natural (path_left Σ j) section_to_disp_alg_map_constr x)
          (endpoint_dact_natural (path_right Σ j) section_to_disp_alg_map_constr x).
    Proof.
      refine (PathOver_square_concat
                apd_section_to_disp_alg_map₁
                _).
      simple refine
             (PathOver_square_1_type
                (PathOver_square_concat
                   apd_section_to_disp_alg_map₂
                   (PathOver_square_1_type
                      (PathOver_square_concat
                         apd_section_to_disp_alg_map₃
                         (PathOver_square_concat
                            apd_section_to_disp_alg_map₄
                            apd_section_to_disp_alg_map₅))))).
      apply TODO.
    Qed.
  End Apd.
  
  Definition section_to_disp_alg_map
    : disp_algebra_map Y.
  Proof.
    unfold disp_algebra_map.
    simple refine (_ ,, _ ,, _).
    - exact section_to_disp_alg_map_comp.
    - exact section_to_disp_alg_map_constr.
    - exact apd_section_to_disp_alg_map.
  Qed.
End SectionToDispAlgMap.
