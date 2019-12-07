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
Require Import displayed_algebras.globe_over_lem.
Require Import displayed_algebras.total_algebra.

Local Open Scope cat.

Local Arguments PathOver {_ _ _} _ _ _ _.

Definition transport_depmap
           {A : UU}
           {Y : A → UU}
           {f : A → A}
           (ff : ∏ (x : A), Y(f x))
           (p : f = λ a, a)
  : ∏ (a : A), Y a
  := λ a, transportf Y (eqtohomot p a) (ff a).

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

Definition poly_pr1_is_id
           {P : poly_code}
           {A : one_type}
           {Y : A → one_type}
           (f : A → total2_one_type Y)
           (p : (λ x, pr1(f x)) = (λ x, x))
           (x : poly_act P A)
  : poly_pr1 P (poly_map P f x) = x.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact (eqtohomot p x).
  - induction x as [x | x].
    + exact (maponpaths inl (IHP₁ x)).
    + exact (maponpaths inr (IHP₂ x)).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Defined.

Definition poly_pr2_is_poly_dmap
           {P : poly_code}
           {A : one_type}
           {Y : A → one_type}
           (f : A → total2_one_type Y)
           (p : (λ x, pr1(f x)) = (λ x, x))
           (x : poly_act P A)
  : PathOver
      (poly_dact_UU P Y)
      (poly_pr2 P _)
      (poly_dmap P Y (transport_depmap (λ z, pr2 (f z)) p) x)
      (poly_pr1_is_id f p x).
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - exact (PathOver_transport (eqtohomot p x) (pr2 (f x))).
  - induction x as [x | x].
    + exact (PathOver_inl (IHP₁ x)).
    + exact (PathOver_inr (IHP₂ x)).
  - exact (PathOver_pair (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Defined.      

Definition PathOver_to_PathOver_transport
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
  simpl in *.
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
      (PathOver_to_PathOver_transport p (apd ff q))
      (idpath _)
      (idpath _).
Proof.
  induction q.
  simpl.
  apply idpath.
Qed.

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

Definition PathOver_square_PathOver_pair
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ : poly_act P A}
           {p₁ p₂ : a₁ = a₂}
           {aa₁ aa₁' : poly_dact P Y a₁} {aa₂ aa₂' : poly_dact P Y a₂}
           {hh₁ : aa₁ = aa₁'} {hh₂ : aa₂ = aa₂'}
           {pp₁ : PathOver (poly_dact P Y) aa₁ aa₂ p₁}
           {pp₂ : PathOver (poly_dact P Y) aa₁' aa₂' p₂}
           {b₁ b₂ : poly_act Q A}
           {q₁ q₂ : b₁ = b₂}
           {bb₁ bb₁' : poly_dact Q Y b₁} {bb₂ bb₂' : poly_dact Q Y b₂}
           {hh₃ : bb₁ = bb₁'} {hh₄ : bb₂ = bb₂'}
           {qq₁ : PathOver (poly_dact Q Y) bb₁ bb₂ q₁}
           {qq₂ : PathOver (poly_dact Q Y) bb₁' bb₂' q₂}
           {s₁ : p₁ = p₂} {s₂ : q₁ = q₂}
           (ps : PathOver_square
                   (poly_dact P Y)
                   s₁
                   pp₁ pp₂
                   hh₁
                   hh₂)
           (qs : PathOver_square
                   (poly_dact Q Y)
                   s₂
                   qq₁ qq₂
                   hh₃
                   hh₄)

  : PathOver_square
      (poly_dact (P * Q) Y)
      (paths_pathsdirprod s₁ s₂)
      (PathOver_pair pp₁ qq₁)
      (PathOver_pair pp₂ qq₂)
      (pathsdirprod hh₁ hh₃)
      (pathsdirprod hh₂ hh₄).
Proof.
  induction hh₁, hh₂, hh₃, hh₄, s₁, p₁, s₂, q₁, ps, pp₁, qs, qq₁.
  apply idpath.
Qed.

Definition PathOver_square_id
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {y₁ :Y a₁} {y₂ : Y a₂}
           (pp : PathOver Y y₁ y₂ p)
  : PathOver_square
      Y
      (idpath _)
      pp
      pp
      (idpath _)
      (idpath _).
Proof.
  apply idpath.
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
           {x₃ x₃' : Y a₃}
           {sl : x₃ = x₃'}
           {pp : PathOver Y x₂ x₃ p₂}
           {qq : PathOver Y x₂ x₃' p₃}
           (rr : PathOver Y x₁ x₂ p₁)
           (s : PathOver_square Y h pp qq (idpath _) sl)
  : PathOver_square
      Y
      (maponpaths (λ z, p₁ @ z) h)
      (composePathOver rr pp)
      (composePathOver rr qq)
      (idpath _)
      sl.
Proof.
  induction h, p₁, p₂, sl, s.
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

(**
`apd_2` but with different implicit arguments`.
More covenient for most upcoming functions
 *)
Definition apd_depfun
           {A B : UU}
           (YA : A → UU) (YB : B → UU)
           {f : A → B}
           (ff : ∏ (a : A), YA a → YB (f a))
           {a b : A}
           {aa : YA a}
           {bb : YA b}
           {q : a = b}
           (qq : PathOver YA aa bb q)
  : PathOver YB (ff a aa) (ff b bb) (maponpaths f q)
  := apd_2 ff q qq.

Definition apd_depfun_idfun
           {A : UU}
           {YA : A → UU}
           {a b : A}
           {aa : YA a}
           {bb : YA b}
           {q : a = b}
           (qq : PathOver YA aa bb q)
  : PathOver_square
      YA
      (!(maponpathsidfun _))
      qq
      (apd_depfun YA YA dep_id_fun qq)
      (idpath _)
      (idpath _).
Proof.
  induction q, qq.
  apply idpath.
Qed.

Definition apd_depfun_inv
           {A B : UU}
           (YA : A → UU) (YB : B → UU)
           {f : A → B}
           (ff : ∏ (a : A), YA a → YB (f a))
           {a b : A}
           {aa : YA a}
           {bb : YA b}
           {q : a = b}
           (qq : PathOver YA aa bb q)
  : PathOver_square
      YB
      (!(maponpathsinv0 _ _))
      (inversePathOver (apd_depfun YA YB ff qq))
      (apd_depfun YA YB ff (inversePathOver qq))
      (idpath _)
      (idpath _).
Proof.
  induction q, qq.
  apply idpath.
Defined.

Definition apd_depfun_concat
           {A B : UU}
           (YA : A → UU) (YB : B → UU)
           {f : A → B}
           (ff : ∏ (a : A), YA a → YB (f a))
           {a b c : A}
           {aa : YA a}
           {bb : YA b}
           {cc : YA c}
           {q : a = b} {q' : b = c}
           (qq : PathOver YA aa bb q)
           (qq' : PathOver YA bb cc q')
  : PathOver_square
      YB
      (!(maponpathscomp0 f q q'))
      (composePathOver
         (apd_depfun YA YB ff qq)
         (apd_depfun YA YB ff qq'))
      (apd_depfun YA YB ff (composePathOver qq qq'))
      (idpath _)
      (idpath _).
Proof.
  induction q, q', qq, qq'.
  apply idpath.
Qed.

Definition apd_depfun_concat_inv
           {A B : UU}
           (YA : A → UU) (YB : B → UU)
           {f : A → B}
           (ff : ∏ (a : A), YA a → YB (f a))
           {a b c : A}
           {aa : YA a}
           {bb : YA b}
           {cc : YA c}
           {q : a = b} {q' : b = c}
           (qq : PathOver YA aa bb q)
           (qq' : PathOver YA bb cc q')
  : PathOver_square
      YB
      (maponpathscomp0 f q q')
      (apd_depfun YA YB ff (composePathOver qq qq'))
      (composePathOver
         (apd_depfun YA YB ff qq)
         (apd_depfun YA YB ff qq'))
      (idpath _)
      (idpath _).
Proof.
  induction q, q', qq, qq'.
  apply idpath.
Qed.

Definition apd_depfun_pr1_PathOver_pair
           {P₁ P₂ : poly_code}
           {A : one_type}
           (YA : A → one_type)
           {x₁ y₁ : poly_act P₁ A} {x₂ y₂ : poly_act P₂ A}
           {p₁ : x₁ = y₁} {p₂ : x₂ = y₂}
           {a₁ : poly_dact_UU P₁ YA x₁} {a₂ : poly_dact_UU P₂ YA x₂}
           {b₁ : poly_dact_UU P₁ YA y₁} {b₂ : poly_dact_UU P₂ YA y₂}
           (pp₁ : PathOver (poly_dact P₁ YA) a₁ b₁ p₁)
           (pp₂ : PathOver (poly_dact P₂ YA) a₂ b₂ p₂)
  : PathOver_square
      (poly_dact P₁ YA)
      (!(maponpaths_pr1_pathsdirprod _ _))
      pp₁
      (apd_depfun
         _ _
         dep_pr1_fun
         (PathOver_pair pp₁ pp₂))
      (idpath _)
      (idpath _).
Proof.
  induction p₁, p₂, pp₁, pp₂.
  apply idpath.
Qed.

Definition apd_depfun_pr2_PathOver_pair
           {P₁ P₂ : poly_code}
           {A : one_type}
           (YA : A → one_type)
           {x₁ y₁ : poly_act P₁ A} {x₂ y₂ : poly_act P₂ A}
           {p₁ : x₁ = y₁} {p₂ : x₂ = y₂}
           {a₁ : poly_dact_UU P₁ YA x₁} {a₂ : poly_dact_UU P₂ YA x₂}
           {b₁ : poly_dact_UU P₁ YA y₁} {b₂ : poly_dact_UU P₂ YA y₂}
           (pp₁ : PathOver (poly_dact P₁ YA) a₁ b₁ p₁)
           (pp₂ : PathOver (poly_dact P₂ YA) a₂ b₂ p₂)
  : PathOver_square
      (poly_dact P₂ YA)
      (!(maponpaths_pr2_pathsdirprod _ _))
      pp₂
      (apd_depfun
         _ _
         dep_pr2_fun
         (PathOver_pair pp₁ pp₂))
      (idpath _)
      (idpath _).
Proof.
  induction p₁, p₂, pp₁, pp₂.
  apply idpath.
Qed.

Definition apd_dep_inl_fun
           {P₁ P₂ : poly_code}
           {A : one_type}
           {YA : A → one_type}
           {x y : poly_act P₁ A}
           {a : poly_dact_UU P₁ YA x}
           {b : poly_dact_UU P₁ YA y}
           {p : x = y}
           (pp : PathOver (poly_dact P₁ YA) a b p)
  : PathOver_square
      (poly_dact_UU (P₁ + P₂) YA)
      (idpath _)
      (PathOver_inl pp)
      (apd_depfun
         _ _
         dep_inl_fun
         pp)
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition apd_dep_inr_fun
           {P₁ P₂ : poly_code}
           {A : one_type}
           {YA : A → one_type}
           {x y : poly_act P₂ A}
           {a : poly_dact_UU P₂ YA x}
           {b : poly_dact_UU P₂ YA y}
           {p : x = y}
           (pp : PathOver (poly_dact P₂ YA) a b p)
  : PathOver_square
      (poly_dact_UU (P₁ + P₂) YA)
      (idpath _)
      (PathOver_inr pp)
      (apd_depfun
         _ _
         dep_inr_fun
         pp)
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition apd_dep_pair_fun
           {P Q R : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {f : poly_act P X → poly_act Q X}
           (ff : ∏ (x : poly_act P X),
                 poly_dact_UU P Y x → poly_dact_UU Q Y (f x))
           {g : poly_act P X → poly_act R X}
           (gg : ∏ (x : poly_act P X),
                 poly_dact_UU P Y x → poly_dact_UU R Y (g x))
           {x y : poly_act P X}
           {a : poly_dact_UU P Y x}
           {b : poly_dact_UU P Y y}
           {p : x = y}
           (pp : PathOver (poly_dact P Y) a b p)
  : PathOver_square
      (poly_dact_UU (Q * R) Y)
      (!(maponpaths_prod_path f g p))
      (PathOver_pair
         (apd_depfun _ _ ff pp)
         (apd_depfun _ _ gg pp))
      (apd_depfun
         _ _
         (dep_pair_fun ff gg)
         pp)
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition apd_dep_comp_fun
           {A B C : UU}
           (YA : A → UU) (YB : B → UU) (YC : C → UU)
           {f : A → B} {g : B → C}
           (ff : ∏ (a : A), YA a → YB (f a))
           (gg : ∏ (b : B), YB b → YC (g b))
           {x y : A}
           {a : YA x}
           {b : YA y}
           {p : x = y}
           (pp : PathOver YA a b p)
  : PathOver_square
      YC
      (maponpathscomp f g p)
      (apd_depfun
         _ _
         gg
         (apd_depfun
            _ _
            ff
            pp))
      (apd_depfun
         _ _
         (dep_comp_fun ff gg)
         pp)
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition maponpaths_for_constant_function
           {X Y : UU}
           (y : Y)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
  : maponpaths (λ _, y) p = idpath _.
Proof.
  induction p.
  apply idpath.
Defined.

Definition apd_depfun_const
           {A T : UU}
           (YA : A → UU) 
           {a b : A}
           (t : T)
           {aa : YA a}
           {bb : YA b}
           {q : a = b}
           (qq : PathOver YA aa bb q)
  : PathOver_square
      (λ _, T)
      (!(maponpaths_for_constant_function t _))
      (identityPathOver t)
      (apd_depfun
         YA
         (λ _ : T, T)
         (λ _ _, t)
         qq)
      (idpath _)
      (idpath _).
Proof.
  induction q, qq.
  apply idpath.
Qed.

Definition PathOver_idpath
           {X : UU}
           {Y : X → UU}
           {x : X}
           {y₁ y₂ : Y x}
           (p : y₁ = y₂)
  : PathOver_square
      Y
      (idpath _)
      (p : PathOver Y y₁ y₂ (idpath x))
      (identityPathOver y₁)
      (idpath _)
      (!p).
Proof.
  induction p.
  apply idpath.
Qed.

Definition PathOver_eq_idpath_to_path
           {X : UU}
           {Y : X → UU}
           {x : X}
           {y₁ y₂ : Y x}
           {p : x = x}
           (h : idpath x = p)
           (pp : PathOver Y y₁ y₂ p)
  : y₁ = y₂.
Proof.
  exact (transportf
           (PathOver Y y₁ y₂)
           (!h)
           pp).
Defined.

Definition PathOver_eq_idpath_to_path_square
           {X : UU}
           {Y : X → UU}
           {x : X}
           {y y' : Y x}
           {p : x = x}
           (h : idpath x = p)
           (pp : PathOver Y y y' p)
  : PathOver_square
      Y
      (!h)
      pp
      (identityPathOver _)
      (idpath _)
      (!(PathOver_eq_idpath_to_path h pp)).
Proof.
  induction h, pp.
  apply idpath.
Qed.

Definition PathOver_natural_help
           {B : UU}
           {YB : B → UU}
           {b₁ b₂ : B}
           {bb₁ : YB b₁} {bb₂ : YB b₂}
           {p : b₁ = b₂}
           (pp : PathOver YB bb₁ bb₂ p)
  : PathOver_square
      YB
      (! (! pathscomp0rid p))
      (composePathOver
         (identityPathOver _)
         (composePathOver
            pp
            (identityPathOver _)))
      pp
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_natural
           {A B : UU}
           {YA : A → UU} {YB : B → UU}
           {f g : A → B}
           {ff : ∏ (a : A), YA a → YB (f a)}
           {gg : ∏ (a : A), YA a → YB (g a)}
           {p : f ~ g}
           (pp : ∏ (z : A) (zz : YA z), PathOver YB (ff z zz) (gg z zz) (p z))
           {a b : A}
           {aa : YA a}
           {bb : YA b}
           {q : a = b}
           (qq : PathOver YA aa bb q)
  : PathOver_square
      YB
      (!(homotsec_natural p q))
      (composePathOver
         (apd_depfun YA YB ff (inversePathOver qq))
         (composePathOver
            (pp a aa)
            (apd_depfun YA YB gg qq)))
      (pp b bb)
      (idpath _)
      (idpath _).
Proof.
  induction q, qq.
  apply PathOver_natural_help.
Qed.

Definition PathOver_square_idpath_r
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : p₁ = p₂}
           {x₁ x₁' : Y a₁}
           {x₂ x₂' : Y a₂}
           {pp : PathOver Y x₁ x₂ p₁}
           {qq : PathOver Y x₁' x₂' p₂}
           {h₁ : x₁  = x₁'} {h₂ : x₂ = x₂'}
           (s : PathOver_square Y h pp qq (h₁ @ idpath _) (h₂ @ idpath _))
  : PathOver_square
      Y
      h
      pp qq
      h₁ h₂.
Proof.
  induction p₁, h, h₁, h₂.
  exact s.
Qed.

Definition PathOver_square_inv_left
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {x₁ : Y a₁}
           {x₂ : Y a₂}
           (pp : PathOver Y x₁ x₂ p)
  : PathOver_square
      Y
      (!(pathsinv0l _))
      (identityPathOver _)
      (composePathOver (inversePathOver pp) pp)
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_square_id_left
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {x₁ : Y a₁}
           {x₂ : Y a₂}
           (pp : PathOver Y x₁ x₂ p)
  : PathOver_square
      Y
      (idpath _)
      (composePathOver (identityPathOver _) pp)
      pp
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_square_id_right
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {x₁ : Y a₁}
           {x₂ : Y a₂}
           (pp : PathOver Y x₁ x₂ p)
  : PathOver_square
      Y
      (pathscomp0rid _)
      (composePathOver pp (identityPathOver _))
      pp
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_square_id_left_inv
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {x₁ : Y a₁}
           {x₂ : Y a₂}
           (pp : PathOver Y x₁ x₂ p)
  : PathOver_square
      Y
      (idpath _)
      pp
      (composePathOver (identityPathOver _) pp)
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_square_move_left
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : p₁ = p₂}
           {y₁ : Y a₁}
           {y₂ y₂' : Y a₂}
           {pp₁ : PathOver Y y₁ y₂ p₁}
           {pp₂ : PathOver Y y₁ y₂' p₂}
           {hr : y₂ = y₂'}
           (ps : PathOver_square
                   Y
                   (maponpaths (λ z, _ @ z) h @ pathsinv0l _)
                   (composePathOver (inversePathOver pp₂) pp₁)
                   (identityPathOver _)
                   (idpath _)
                   hr)
  : PathOver_square
      Y
      h
      pp₁
      pp₂
      (idpath _)
      hr.
Proof.
  induction h, p₁, hr, pp₂.
  simpl in *.
  exact ps.
Qed.

Definition PathOver_square_move_right
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : p₁ = p₂}
           {y₁ y₁' : Y a₁}
           {y₂ : Y a₂}
           {pp₁ : PathOver Y y₁ y₂ p₁}
           {pp₂ : PathOver Y y₁' y₂ p₂}
           {hr : y₁ = y₁'}
           (ps : PathOver_square
                   Y
                   h
                   pp₁
                   pp₂
                   hr
                   (idpath _))
  : PathOver_square
      Y
      (maponpaths (λ z, z @ _) h @ pathsinv0r _)
      (composePathOver pp₁ (inversePathOver pp₂))
      (identityPathOver _)
      (idpath _)
      (!hr).
Proof.
  induction h, p₁, hr, pp₂.
  simpl in *.
  exact (pathscomp0rid _ @ ps).
Qed.

Definition inversePathOver_compose
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ a₃ : A}
           {p : a₁ = a₂} {q : a₂ = a₃}
           {x₁ : Y a₁}
           {x₂ : Y a₂}
           {x₃ : Y a₃}
           (pp : PathOver Y x₁ x₂ p)
           (qq : PathOver Y x₂ x₃ q)
  : PathOver_square
      Y
      (pathscomp_inv p q)
      (inversePathOver (composePathOver pp qq))
      (composePathOver (inversePathOver qq) (inversePathOver pp))
      (idpath _)
      (idpath _).
Proof.
  induction p, q, pp, qq.
  apply idpath.
Qed.

Definition inversePathOver_inversePathOver
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p : a₁ = a₂}
           {x₁ : Y a₁}
           {x₂ : Y a₂}
           (pp : PathOver Y x₁ x₂ p)
  : PathOver_square
      Y
      (pathsinv0inv0 p)
      (inversePathOver (inversePathOver pp))
      pp
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition inversePathOver_PathOver_square
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : p₁ = p₂}
           {y₁ z₁ : Y a₁} {y₂ z₂ : Y a₂}
           {pp₁ : PathOver Y y₁ y₂ p₁}
           {pp₂ : PathOver Y z₁ z₂ p₂}
           {h₁ : y₁ = z₁}
           {h₂ : y₂ = z₂}
           (ps : PathOver_square Y h pp₁ pp₂ h₁ h₂)
  : PathOver_square
      Y
      (maponpaths (λ z, !z) h)
      (inversePathOver pp₁)
      (inversePathOver pp₂)
      h₂
      h₁.
Proof.
  induction h₁, h₂.
  induction p₁, h, pp₁, ps.
  apply idpath.
Qed.

Definition inverse_PathOver_square
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : p₁ = p₂}
           {y₁ z₁ : Y a₁} {y₂ z₂ : Y a₂}
           {pp₁ : PathOver Y y₁ y₂ p₁}
           {pp₂ : PathOver Y z₁ z₂ p₂}
           {h₁ : z₁ = y₁}
           {h₂ : z₂ = y₂}
           (ps : PathOver_square Y h pp₁ pp₂ (!h₁) (!h₂))
  : PathOver_square
      Y
      (!h)
      pp₂
      pp₁
      h₁
      h₂.
Proof.
  induction h₁, h₂.
  induction p₁, h, pp₁, ps.
  apply idpath.
Qed.

Definition PathOver_square_inverse
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : p₁ = p₂}
           {y₁ z₁ : Y a₁} {y₂ z₂ : Y a₂}
           {pp₁ : PathOver Y y₁ y₂ p₁}
           {pp₂ : PathOver Y z₁ z₂ p₂}
           {h₁ : y₁ = z₁}
           {h₂ : y₂ = z₂}
           (ps : PathOver_square Y h pp₁ pp₂ h₁ h₂)
  : PathOver_square
      Y
      (!h)
      pp₂
      pp₁
      (!h₁)
      (!h₂).
Proof.
  induction h₁, h₂.
  induction p₁, h, pp₁, ps.
  apply idpath.
Qed.

Definition inversePathOver_PathOver_square_inj
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : ! p₁ = ! p₂}
           {y₁ z₁ : Y a₁} {y₂ z₂ : Y a₂}
           {pp₁ : PathOver Y y₁ y₂ p₁}
           {pp₂ : PathOver Y z₁ z₂ p₂}
           {h₁ : y₁ = z₁}
           {h₂ : y₂ = z₂}
           (ps : PathOver_square
                   Y
                   h
                   (inversePathOver pp₁) (inversePathOver pp₂)
                   h₂ h₁)
  : PathOver_square
      Y
      (!(pathsinv0inv0 _) @ maponpaths (λ z, !z) h @ pathsinv0inv0 _)
      pp₁ pp₂
      h₁ h₂.
Proof.
  refine (PathOver_square_1_type _).
  refine (PathOver_square_concat
            (PathOver_square_inverse (inversePathOver_inversePathOver pp₁))
            _).
  apply PathOver_square_idpath_r.
  exact (PathOver_square_concat
           (inversePathOver_PathOver_square ps)
           (inversePathOver_inversePathOver pp₂)).
Qed.


Definition ap_sigma_to_apd
           {A : one_type}
           {Y : A → UU}
           (f : A → ∑ (x : A), Y x)
           (e : (λ a, pr1 (f a)) = λ a, a)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : PathOver_square
      Y
      (ap_sigma_to_apd_help f e p)
      (PathOver_to_PathOver_transport
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
  exact (PathOver_square_1_type
           (PathOver_square_concat
              (PathOver_square_inv_left
                 (PathOver_transport (eqtohomot e a₁) (pr2 (f a₁))))
              (PathOver_square_comp_l
                 _
                 (PathOver_square_id_left_inv
                    (PathOver_transport (eqtohomot e a₁) (pr2 (f a₁))))))).
Qed.

Definition poly_dact_TotalPathToPathOver
           (P : poly_code)
           {X : one_type}
           {Y : X → one_types}
           {x y : poly_act P (total2_one_type Y)}
           (p : x = y)
  : PathOver
      (poly_dact P Y)
      (poly_pr2 P x)
      (poly_pr2 P y)
      (maponpaths (poly_pr1 P) p).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl.
  - induction p.
    apply idpath.
  - exact (TotalPathToPathOver p).
  - induction p.
    induction x as [x | x].
    + exact (IHP₁ x x (idpath _)).
    + exact (IHP₂ x x (idpath _)).
  - induction p.
    exact (pathsdirprod
             (IHP₁ _ _ (idpath _))
             (IHP₂ _ _ (idpath _))).
Defined.

Definition poly_dact_TotalPathToPathOver_idpath
           (P : poly_code)
           {X : one_type}
           {Y : X → one_types}
           (x : poly_act P (total2_one_type Y))
  : PathOver_square
      (poly_dact P Y)
      (idpath _)
      (poly_dact_TotalPathToPathOver P (idpath x))
      (identityPathOver _)
      (idpath _)
      (idpath _).
Proof.
  simpl.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + apply IHP₁.
    + apply IHP₂.
  - exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition poly_dact_TotalPathToPathOver_concat
           (P : poly_code)
           {X : one_type}
           {Y : X → one_types}
           {x y z : poly_act P (total2_one_type Y)}
           (p : x = y) (q : y = z)
  : PathOver_square
      (poly_dact P Y)
      (maponpathscomp0 _ _ _)
      (poly_dact_TotalPathToPathOver P (p @ q))
      (composePathOver
         (poly_dact_TotalPathToPathOver P p)
         (poly_dact_TotalPathToPathOver P q))
      (idpath _)
      (idpath _).
Proof.
  induction p, q.
  simpl.
    induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + apply IHP₁.
    + apply IHP₂.
  - simpl.
    refine (_ @ !(pathsdirprod_concat _ _ _ _)).
    exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition poly_dact_PathOver_transport
           {P : poly_code}
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : poly_act P X}
           (p : x₁ = x₂)
           (y : poly_dact_UU P Y x₁)
  : PathOver
      (poly_dact_UU P Y)
      y
      (transportf (poly_dact_UU P Y) p y)
      p.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl.
  - induction p.
    apply idpath.
  - exact (PathOver_transport p y).
  - induction p.
    induction x₁ as [x₁ | x₁].
    + exact (IHP₁ _ _ (idpath _) y).
    + exact (IHP₂ _ _ (idpath _) y).
  - induction p.
    exact (pathsdirprod
             (IHP₁ _ _ (idpath _) (pr1 y))
             (IHP₂ _ _ (idpath _) (pr2 y))).
Defined.

Definition poly_dact_PathOver_transport_idpath
           {P : poly_code}
           {X : UU}
           {Y : X → UU}
           (x : poly_act P X)
           (y : poly_dact_UU P Y x)
  : poly_dact_PathOver_transport (idpath x) y = idpath y.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl.
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + apply IHP₁.
    + apply IHP₂.
  - exact (paths_pathsdirprod (IHP₁ _ (pr1 y)) (IHP₂ _ (pr2 y))).
Qed.

Definition PathOver_square_conj
           {X : UU}
           {Y : X → UU}
           {a₁ a₂ a₃ a₄ : X}
           {p₁ q₁ : a₁ = a₂}
           {p₂ : a₂ = a₃}
           {p₃ q₃ : a₃ = a₄}
           {h₁ : p₁ = q₁} {h₃ : p₃ = q₃}
           {y₁ z₁ : Y a₁} {y₂ : Y a₂}
           {y₃ : Y a₃} {y₄ z₄ : Y a₄}
           {pp₁ : PathOver Y y₁ y₂ p₁} {pp₁' : PathOver Y z₁ y₂ q₁}
           (pp₂ : PathOver Y y₂ y₃ p₂)
           {pp₃ : PathOver Y y₃ y₄ p₃} {pp₃' : PathOver Y y₃ z₄ q₃}
           {l₁ : y₁ = z₁} {l₄ : y₄ = z₄}
           (sq₁ : PathOver_square
                    Y
                    h₁
                    pp₁
                    pp₁'
                    l₁
                    (idpath _))
           (sq₂ : PathOver_square
                    Y
                    h₃
                    pp₃
                    pp₃'
                    (idpath _)
                    l₄)
  : PathOver_square
      Y
      (maponpaths (λ z, z @ _ @ _) h₁ @ maponpaths (λ z, _ @ _ @ z) h₃)
      (composePathOver
         pp₁
         (composePathOver
            pp₂
            pp₃))
      (composePathOver
         pp₁'
         (composePathOver
            pp₂
            pp₃'))
      l₁
      l₄.
Proof.
  induction h₁, h₃, l₁, l₄, p₁, p₂, p₃.
  simpl in *.
  exact (maponpaths (λ z, z @ _ @ _) sq₁ @ maponpaths (λ z, _ @ _ @ z) sq₂).
Qed.

Definition apd_depfun_inl_help
           {P₁ P₂ : poly_code}
           {A : one_type}
           (YA : A → one_type)
           {x y : poly_act P₁ A}
           {p : x = y}
           {a : poly_dact_UU P₁ YA x}
           {b : poly_dact_UU P₁ YA y}
           (pp : PathOver (poly_dact P₁ YA) a b p)
  : transportf (poly_dact_UU (P₁ + P₂) (λ x0 : A, YA x0)) (maponpaths inl p) a = b.
Proof.
  induction p.
  exact pp.
Defined.

Definition apd_depfun_inl
           {P₁ P₂ : poly_code}
           {A : one_type}
           (YA : A → one_type)
           {x y : poly_act P₁ A}
           {p : x = y}
           {a : poly_dact_UU P₁ YA x}
           {b : poly_dact_UU P₁ YA y}
           (pp : PathOver (poly_dact P₁ YA) a b p)
  : PathOver_square
      (poly_dact (P₁ + P₂) YA)
      (idpath _)
      (@poly_dact_PathOver_transport
         (P₁ + P₂)
         A YA
         _ _
         _ _)
      (@apd_depfun
         _ _
         (poly_dact P₁ YA)
         (poly_dact (P₁ + P₂) YA)
         inl
         (λ _ z, z)
         _ _ _ _ _
         pp)
      (idpath _)
      (apd_depfun_inl_help YA pp).
Proof.
  induction p, pp.
  apply poly_dact_PathOver_transport_idpath.
Qed.

Definition apd_depfun_inr_help
           {P₁ P₂ : poly_code}
           {A : one_type}
           (YA : A → one_type)
           {x y : poly_act P₂ A}
           {p : x = y}
           {a : poly_dact_UU P₂ YA x}
           {b : poly_dact_UU P₂ YA y}
           (pp : PathOver (poly_dact P₂ YA) a b p)
  : transportf (poly_dact_UU (P₁ + P₂) (λ x0 : A, YA x0)) (maponpaths inr p) a = b.
Proof.
  induction p.
  exact pp.
Defined.

Definition apd_depfun_inr
           {P₁ P₂ : poly_code}
           {A : one_type}
           (YA : A → one_type)
           {x y : poly_act P₂ A}
           {p : x = y}
           {a : poly_dact_UU P₂ YA x}
           {b : poly_dact_UU P₂ YA y}
           (pp : PathOver (poly_dact P₂ YA) a b p)
  : PathOver_square
      (poly_dact (P₁ + P₂) YA)
      (idpath _)
      (@poly_dact_PathOver_transport
         (P₁ + P₂)
         A YA
         _ _
         _ _)
      (@apd_depfun
         _ _
         (poly_dact P₂ YA)
         (poly_dact (P₁ + P₂) YA)
         inr
         (λ _ z, z)
         _ _ _ _ _
         pp)
      (idpath _)
      (apd_depfun_inr_help YA pp).
Proof.
  induction p, pp.
  apply poly_dact_PathOver_transport_idpath.
Qed.

Definition PathOver_square_path_left
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : p₁ = p₂}
           {y₁ y₁' : Y a₁} {y₂ y₂' : Y a₂}
           {pp₁ : PathOver Y y₁ y₂ p₁}
           {pp₂ : PathOver Y y₁' y₂' p₂}
           {h₁ h₁' : y₁ = y₁'} {h₂ : y₂ = y₂'}
           (ps : PathOver_square
                   Y
                   h
                   pp₁ pp₂
                   h₁ h₂)
           (r : h₁ = h₁')
  : PathOver_square
      Y
      h
      pp₁ pp₂
      h₁' h₂.
Proof.
  induction r.
  exact ps.
Qed.

Definition PathOver_square_path_right
           {A : UU}
           {Y : A → UU}
           {a₁ a₂ : A}
           {p₁ p₂ : a₁ = a₂}
           {h : p₁ = p₂}
           {y₁ y₁' : Y a₁} {y₂ y₂' : Y a₂}
           {pp₁ : PathOver Y y₁ y₂ p₁}
           {pp₂ : PathOver Y y₁' y₂' p₂}
           {h₁ : y₁ = y₁'} {h₂ h₂' : y₂ = y₂'}
           (ps : PathOver_square
                   Y
                   h
                   pp₁ pp₂
                   h₁ h₂)
           (r : h₂ = h₂')
  : PathOver_square
      Y
      h
      pp₁ pp₂
      h₁ h₂'.
Proof.
  induction r.
  exact ps.
Qed.

Definition compose_PathOver_pair
           {P₁ P₂ : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ a₃ : poly_act P₁ A}
           {pa₁ : a₁ = a₂} {pa₂ : a₂ = a₃}
           {ya₁ : poly_dact P₁ Y a₁}
           {ya₂ : poly_dact P₁ Y a₂}
           {ya₃ : poly_dact P₁ Y a₃}
           (ppa₁ : PathOver (poly_dact P₁ Y) ya₁ ya₂ pa₁)
           (ppa₂ : PathOver (poly_dact P₁ Y) ya₂ ya₃ pa₂)
           {b₁ b₂ b₃ : poly_act P₂ A}
           {pb₁ : b₁ = b₂} {pb₂ : b₂ = b₃}
           {yb₁ : poly_dact P₂ Y b₁}
           {yb₂ : poly_dact P₂ Y b₂}
           {yb₃ : poly_dact P₂ Y b₃}
           (ppb₁ : PathOver (poly_dact P₂ Y) yb₁ yb₂ pb₁)
           (ppb₂ : PathOver (poly_dact P₂ Y) yb₂ yb₃ pb₂)
  : PathOver_square
      (poly_dact_UU (P₁ * P₂) Y)
      (pathsdirprod_concat _ _ _ _)
      (composePathOver
         (PathOver_pair ppa₁ ppb₁)
         (PathOver_pair ppa₂ ppb₂))
      (PathOver_pair
         (composePathOver ppa₁ ppa₂)
         (composePathOver ppb₁ ppb₂))
      (idpath _)
      (idpath _).
Proof.
  induction pa₁, pa₂, pb₁, pb₂, ppa₁, ppa₂, ppb₁, ppb₂.
  apply idpath.
Qed.

Definition inverse_PathOverPair
           {P₁ P₂ : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ : poly_act P₁ A}
           {pa : a₁ = a₂}
           {ya₁ : poly_dact P₁ Y a₁}
           {ya₂ : poly_dact P₁ Y a₂}
           (ppa : PathOver (poly_dact P₁ Y) ya₁ ya₂ pa)
           {b₁ b₂ : poly_act P₂ A}
           {pb : b₁ = b₂}
           {yb₁ : poly_dact P₂ Y b₁}
           {yb₂ : poly_dact P₂ Y b₂}
           (ppb : PathOver (poly_dact P₂ Y) yb₁ yb₂ pb)
  : PathOver_square
      (poly_dact_UU (P₁ * P₂) Y)
      (pathsdirprod_inv _ _)
      (inversePathOver (PathOver_pair ppa ppb))
      (PathOver_pair
         (inversePathOver ppa)
         (inversePathOver ppb))
      (idpath _)
      (idpath _).
Proof.
  induction pa, ppa, pb, ppb.
  apply idpath.
Qed.

Definition poly_dact_TotalPathToPathOver_inl
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act P (total2_one_type Y)}
           (p : x₁ = x₂)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (coprodf_path_maponpaths_inl _ _ _)
      (poly_dact_TotalPathToPathOver
         (P + Q)
         (maponpaths inl p))
      (PathOver_inl (poly_dact_TotalPathToPathOver P p))
      (idpath _)
      (idpath _).
Proof.
  induction p.
  apply idpath.
Qed.

Definition poly_dact_TotalPathToPathOver_inr
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act Q (total2_one_type Y)}
           (p : x₁ = x₂)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (coprodf_path_maponpaths_inr _ _ _)
      (poly_dact_TotalPathToPathOver
         (P + Q)
         (maponpaths inr p))
      (PathOver_inr (poly_dact_TotalPathToPathOver Q p))
      (idpath _)
      (idpath _).
Proof.
  induction p.
  apply idpath.
Qed.

Definition poly_dact_TotalPathToPathOver_pathsdirprod
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act P (total2_one_type Y)}
           (p : x₁ = x₂)
           {y₁ y₂ : poly_act Q (total2_one_type Y)}
           (q : y₁ = y₂)
  : PathOver_square
      (poly_dact (P * Q) Y)
      (!(maponpaths_pathsdirprod _ _ _ _))
      (poly_dact_TotalPathToPathOver
         (P * Q)
         (pathsdirprod p q))
      (PathOver_pair
         (poly_dact_TotalPathToPathOver P p)
         (poly_dact_TotalPathToPathOver Q q))
      (idpath _)
      (idpath _).
Proof.
  induction p, q.
  apply idpath.
Qed.

Definition PathOver_square_PathOver_inl
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ : poly_act P A}
           {p q : a₁ = a₂}
           {h : p = q}
           {y₁ y₁' : poly_dact P Y a₁}
           {y₂ y₂' : poly_dact P Y a₂}
           {hl : y₁ = y₁'} {hr : y₂ = y₂'}
           (pp : PathOver (poly_dact P Y) y₁ y₂ p)
           (qq : PathOver (poly_dact P Y) y₁' y₂' q)
           (ps : PathOver_square
                   (poly_dact P Y)
                   h
                   pp
                   qq
                   hl
                   hr)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (maponpaths (maponpaths inl) h)
      (PathOver_inl pp)
      (PathOver_inl qq)
      hl
      hr.
Proof.
  induction hl, hr, h, p, ps.
  apply idpath.
Qed.

Definition PathOver_square_PathOver_inr
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ : poly_act Q A}
           {p q : a₁ = a₂}
           {h : p = q}
           {y₁ y₁' : poly_dact Q Y a₁}
           {y₂ y₂' : poly_dact Q Y a₂}
           {hl : y₁ = y₁'} {hr : y₂ = y₂'}
           (pp : PathOver (poly_dact Q Y) y₁ y₂ p)
           (qq : PathOver (poly_dact Q Y) y₁' y₂' q)
           (ps : PathOver_square
                   (poly_dact Q Y)
                   h
                   pp
                   qq
                   hl
                   hr)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (maponpaths (maponpaths inr) h)
      (PathOver_inr pp)
      (PathOver_inr qq)
      hl
      hr.
Proof.
  induction hl, hr, h, p, ps.
  apply idpath.
Qed.

Definition PathOver_inl_inverse
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ : poly_act P A}
           {p : a₁ = a₂}
           {y₁ : poly_dact P Y a₁}
           {y₂ : poly_dact P Y a₂}
           (pp : PathOver (poly_dact P Y) y₁ y₂ p)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (!(maponpathsinv0 inl p))
      (inversePathOver (PathOver_inl pp))
      (PathOver_inl (inversePathOver pp))
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_inr_inverse
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ : poly_act Q A}
           {p : a₁ = a₂}
           {y₁ : poly_dact Q Y a₁}
           {y₂ : poly_dact Q Y a₂}
           (pp : PathOver (poly_dact Q Y) y₁ y₂ p)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (!(maponpathsinv0 inr p))
      (inversePathOver (PathOver_inr pp))
      (PathOver_inr (inversePathOver pp))
      (idpath _)
      (idpath _).
Proof.
  induction p, pp.
  apply idpath.
Qed.

Definition PathOver_inl_compose
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ a₃ : poly_act P A}
           {p : a₁ = a₂} {q : a₂ = a₃}
           {y₁ : poly_dact P Y a₁}
           {y₂ : poly_dact P Y a₂}
           {y₃ : poly_dact P Y a₃}
           (pp : PathOver (poly_dact P Y) y₁ y₂ p)
           (qq : PathOver (poly_dact P Y) y₂ y₃ q)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (!(maponpathscomp0 inl p q))
      (composePathOver
         (PathOver_inl pp)
         (PathOver_inl qq))
      (PathOver_inl (composePathOver pp qq))
      (idpath _)
      (idpath _).
Proof.
  induction p, q, pp, qq.
  apply idpath.
Qed.

Definition PathOver_inr_compose
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {a₁ a₂ a₃ : poly_act Q A}
           {p : a₁ = a₂} {q : a₂ = a₃}
           {y₁ : poly_dact Q Y a₁}
           {y₂ : poly_dact Q Y a₂}
           {y₃ : poly_dact Q Y a₃}
           (pp : PathOver (poly_dact Q Y) y₁ y₂ p)
           (qq : PathOver (poly_dact Q Y) y₂ y₃ q)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (!(maponpathscomp0 inr p q))
      (composePathOver
         (PathOver_inr pp)
         (PathOver_inr qq))
      (PathOver_inr (composePathOver pp qq))
      (idpath _)
      (idpath _).
Proof.
  induction p, q, pp, qq.
  apply idpath.
Qed.

    
Definition apd_depfun2
           {A : UU} {B : UU}
           (YA : A → UU)
           (YB : B → UU)
           {f : A → B}
           (ff : ∏ (a : A), YA a → YB (f a))
           {a b : A}
           {aa aa' : YA a} {bb bb' : YA b}
           {p₁ p₂ : a = b}
           {h : p₁ = p₂}
           {pp₁ : PathOver YA aa bb p₁}
           {pp₂ : PathOver YA aa' bb' p₂}
           {hl : aa = aa'} {hr : bb = bb'}
           (ps : PathOver_square
                   YA
                   h
                   pp₁
                   pp₂
                   hl
                   hr)
  : PathOver_square
      YB
      (maponpaths (maponpaths f) h)
      (apd_depfun YA YB ff pp₁)
      (apd_depfun YA YB ff pp₂)
      (maponpaths (ff a) hl)
      (maponpaths (ff b) hr).
Proof.
  induction h, p₁, hl, hr, pp₁, ps.
  apply idpath.
Qed.

Definition apd_section_endpoint
           {Σ : hit_signature}
           {P Q : poly_code}
           (e : endpoint (point_constr Σ) P Q)
           {X : hit_algebra_one_types Σ}
           {Y : disp_algebra X}
           (f : X --> total_algebra Y)
           (p : (λ a, pr1 ((pr111 f) a)) = (λ a, a))
           (x : poly_act P (alg_carrier X))
  := composePathOver
       (inversePathOver
          (poly_dact_PathOver_transport
             (poly_pr1_is_id _ p _)
             _))
       (composePathOver
          (poly_dact_TotalPathToPathOver
             _
             (sem_endpoint_UU_natural e (pr121 (pr1 f)) x))
          (inversePathOver
             (total_algebra.pr2_endpoint
                Y e
                (poly_map P (pr111 f) x)))).

Definition inv_apd_section_endpoint
           {Σ : hit_signature}
           {P Q : poly_code}
           (e : endpoint (point_constr Σ) P Q)
           {X : hit_algebra_one_types Σ}
           {Y : disp_algebra X}
           (f : X --> total_algebra Y)
           (p : (λ a, pr1 ((pr111 f) a)) = (λ a, a))
           (x : poly_act P (alg_carrier X))
  := composePathOver
       (total_algebra.pr2_endpoint
             Y e
             (poly_map P (pr111 f) x))
       (composePathOver
          (inversePathOver
             (poly_dact_TotalPathToPathOver
                _
                (sem_endpoint_UU_natural e (pr121 (pr1 f)) x)))
          (poly_dact_PathOver_transport
             (poly_pr1_is_id _ p _)
             _)).

Definition maponpaths_sem_endpoint_UU
           {Σ : hit_signature}
           {P Q : poly_code}
           (e : endpoint (point_constr Σ) P Q)
           {X : hit_algebra_one_types Σ}
           {Y : disp_algebra X}
           (f : X --> total_algebra Y)
           (p : (λ a, pr1 ((pr111 f) a)) = (λ a, a))
           (pc : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
                 !(eqtohomot p ((pr211 X) x)) @ maponpaths pr1 ((pr121 (pr1 f)) x)
                 =
                 maponpaths (pr211 X) (! poly_pr1_is_id (pr111 f) p x))
           (x : poly_act P (alg_carrier X))
  : !(poly_pr1_is_id (pr111 f) p (sem_endpoint_UU e (pr211 X) x))
  @ maponpaths (poly_pr1 Q) (sem_endpoint_UU_natural e (pr121 (pr1 f)) x)
  @ !(total_algebra.pr1_endpoint Y e (poly_map P (pr111 f) x))
  =
  maponpaths (sem_endpoint_UU e (pr211 X)) (! poly_pr1_is_id (pr111 f) p x).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ g | ].
  - exact (pathscomp0rid _ @ !(maponpathsidfun _)).
  - simpl.
    refine (!_).
    etrans.
    {
      refine (!_).
      apply maponpathscomp.
    }
    etrans.
    {
      apply maponpaths.
      exact (!(IHe₁ _)).
    }
    etrans.
    {
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths_2.
      exact (!(IHe₂ _)).
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply maponpathscomp0.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply pathscomp_inv.
      }
      apply maponpaths.
      exact (!(maponpathsinv0 _ _)).
    }
    refine (path_assoc _ _ _ @ _).
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp.
    }
    etrans.
    {
      apply (homotsec_natural'
               (λ z, ! total_algebra.pr1_endpoint Y e₂ z)).
    }
    apply maponpaths.
    exact (!(maponpathscomp _ _ _)).
  - exact (pathscomp0rid _ @ !(maponpathsinv0 _ _)).
  - exact (pathscomp0rid _ @ !(maponpathsinv0 _ _)).
  - simpl.
    refine (pathscomp0rid _ @ _).
    refine (_ @ !(maponpaths (maponpaths pr1) (pathsdirprod_inv _ _))).
    exact (!(maponpaths_pr1_pathsdirprod _ _)).
  - simpl.
    refine (pathscomp0rid _ @ _).
    refine (_ @ !(maponpaths (maponpaths dirprod_pr2) (pathsdirprod_inv _ _))).
    exact (!(maponpaths_pr2_pathsdirprod _ _)).
  - simpl.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_inv.
        }
        etrans.
        {
          apply maponpaths_2.
          exact (!(maponpaths_pathsdirprod _ _ _ _)).
        }
        apply pathsdirprod_concat.
      }
      etrans.
      {
        apply maponpaths_2.
        apply pathsdirprod_inv.
      }
      apply pathsdirprod_concat.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_prod_path.
    }
    refine (!_).
    exact (paths_pathsdirprod (IHe₁ _) (IHe₂ _)).
  - exact (!(maponpaths_for_constant_function _ _)).
  - apply idpath.
  - simpl.
    etrans.
    {
      apply maponpaths.
      apply pathscomp0rid.
    }
    exact (pc x).
Qed.

Definition transportf_poly_dact_inl
           {P₁ P₂ : poly_code}
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : poly_act P₁ X}
           (p : x₁ = x₂)
           (y : poly_dact_UU P₁ Y x₁)
  : transportf (poly_dact_UU (P₁ + P₂) Y) (maponpaths inl p) y
    =
    transportf (poly_dact_UU P₁ Y) p y.
Proof.
  induction p.
  apply idpath.
Defined.

Definition transportf_poly_dact_inr
           {P₁ P₂ : poly_code}
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : poly_act P₂ X}
           (p : x₁ = x₂)
           (y : poly_dact_UU P₂ Y x₁)
  : transportf (poly_dact_UU (P₁ + P₂) Y) (maponpaths inr p) y
    =
    transportf (poly_dact_UU P₂ Y) p y.
Proof.
  induction p.
  apply idpath.
Defined.

Definition transportf_poly_dact_pair
           {P₁ P₂ : poly_code}
           {X : UU}
           {Y : X → UU}
           {x₁ x₂ : poly_act P₁ X}
           {y₁ y₂ : poly_act P₂ X}
           (p : x₁ = x₂) (q : y₁ = y₂)
           (z₁ : poly_dact_UU P₁ Y x₁) (z₂ : poly_dact_UU P₂ Y y₁)
  : transportf (poly_dact_UU (P₁ * P₂) Y) (pathsdirprod p q) (z₁ ,, z₂)
    =
    transportf (poly_dact_UU P₁ Y) p z₁ ,, transportf (poly_dact_UU P₂ Y) q z₂.
Proof.
  induction p, q.
  apply idpath.
Defined.

Definition poly_dact_PathOver_transport_inl
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act P A}
           (p : x₁ = x₂)
           (xx₁ : poly_dact P Y x₁)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (idpath _)
      (@poly_dact_PathOver_transport
         (P + Q)
         A Y
         _ _
         (maponpaths inl p)
         xx₁)
      (PathOver_inl (poly_dact_PathOver_transport p xx₁))
      (idpath _)
      (transportf_poly_dact_inl _ _).
Proof.
  induction p.
  apply idpath.
Qed.

Definition poly_dact_PathOver_transport_inl_alt
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act P A}
           (p : x₁ = x₂)
           (xx₁ : poly_dact P Y x₁)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (pathscomp0rid _)
      (composePathOver
         (@poly_dact_PathOver_transport
            (P + Q)
            A Y
            _ _
            (maponpaths inl p)
            xx₁)
         (transportf_poly_dact_inl _ _ : PathOver _ _ _ (idpath _)))
      (PathOver_inl (poly_dact_PathOver_transport p xx₁))
      (idpath _)
      (idpath _).
Proof.
  induction p.
  apply pathscomp0rid.
Qed.

Definition poly_dact_PathOver_transport_inr
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act Q A}
           (p : x₁ = x₂)
           (xx₁ : poly_dact Q Y x₁)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (idpath _)
      (@poly_dact_PathOver_transport
         (P + Q)
         A Y
         _ _
         (maponpaths inr p)
         xx₁)
      (PathOver_inr (poly_dact_PathOver_transport p xx₁))
      (idpath _)
      (transportf_poly_dact_inr _ _).
Proof.
  induction p.
  apply idpath.
Qed.

Definition poly_dact_PathOver_transport_inr_alt
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act Q A}
           (p : x₁ = x₂)
           (xx₁ : poly_dact Q Y x₁)
  : PathOver_square
      (poly_dact (P + Q) Y)
      (pathscomp0rid _)
      (composePathOver
         (@poly_dact_PathOver_transport
            (P + Q)
            A Y
            _ _
            (maponpaths inr p)
            xx₁)
         (transportf_poly_dact_inr _ _ : PathOver _ _ _ (idpath _)))
      (PathOver_inr (poly_dact_PathOver_transport p xx₁))
      (idpath _)
      (idpath _).
Proof.
  induction p.
  apply pathscomp0rid.
Qed.

Definition poly_dact_PathOver_transport_pathsdirprod
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act P A}
           (p : x₁ = x₂)
           (xx₁ : poly_dact P Y x₁)
           {y₁ y₂ : poly_act Q A}
           (q : y₁ = y₂)
           (yy₁ : poly_dact Q Y y₁)
  : PathOver_square
      (poly_dact (P * Q) Y)
      (idpath _)
      (@poly_dact_PathOver_transport
         (P * Q)
         A Y
         _ _
         (pathsdirprod p q)
         (xx₁ ,, yy₁))
      (PathOver_pair
         (poly_dact_PathOver_transport p xx₁)
         (poly_dact_PathOver_transport q yy₁))
      (idpath _)
      (transportf_poly_dact_pair p q _ _).
Proof.
  induction p, q.
  apply idpath.
Qed.

Definition poly_dact_PathOver_transport_pathsdirprod_alt
           {P Q : poly_code}
           {A : one_type}
           {Y : A → one_type}
           {x₁ x₂ : poly_act P A}
           (p : x₁ = x₂)
           (xx₁ : poly_dact P Y x₁)
           {y₁ y₂ : poly_act Q A}
           (q : y₁ = y₂)
           (yy₁ : poly_dact Q Y y₁)
  : PathOver_square
      (poly_dact (P * Q) Y)
      (pathscomp0rid _)
      (composePathOver
         (@poly_dact_PathOver_transport
            (P * Q)
            A Y
            _ _
            (pathsdirprod p q)
            (xx₁ ,, yy₁))
         (transportf_poly_dact_pair p q _ _ : PathOver _ _ _ (idpath _)))
      (PathOver_pair
         (poly_dact_PathOver_transport p xx₁)
         (poly_dact_PathOver_transport q yy₁))
      (idpath _)
      (idpath _).
Proof.
  induction p, q.
  apply pathscomp0rid.
Qed.

Definition total_algebra_pr2_endpoint_natural
           {Σ : hit_signature}
           {X : hit_algebra_one_types Σ}
           {Y : disp_algebra X}
           {P Q : poly_code}
           (e : endpoint (point_constr Σ) P Q)
           {x y : poly_act P (total_algebra.carrier Y)}
           (p : y = x)
  : ∑ q,
    PathOver_square
      (poly_dact Q (pr1 Y))
      q
      (composePathOver
         (total_algebra.pr2_endpoint Y e x)
         (inversePathOver
            (poly_dact_TotalPathToPathOver
               Q
               (maponpaths
                  (sem_endpoint_UU e (total_algebra.operation Y))
                  p))))
      (composePathOver
         (apd_depfun
            (poly_dact P (pr1 Y))
            (poly_dact Q (pr1 Y))
            (@endpoint_dact (point_constr Σ) (pr11 X) (pr1 Y) P Q e (disp_alg_constr Y))
            (inversePathOver
               (poly_dact_TotalPathToPathOver P p)))
         (total_algebra.pr2_endpoint Y e y))
      (idpath _)
      (idpath _).
Proof.
  induction p.
  refine (_ ,, _).
  refine
    (PathOver_square_concat
       (PathOver_square_comp_l
          _
          (inversePathOver_PathOver_square
             (poly_dact_TotalPathToPathOver_idpath _ _)))
       (PathOver_square_concat
          (PathOver_square_id_right _)
          _)).
  refine (inverse_PathOver_square _).
  exact
    (PathOver_square_concat
       (PathOver_square_comp_r
          _
          (apd_depfun2
             (poly_dact P (pr1 Y))
             (poly_dact Q (pr1 Y))
             (@endpoint_dact (point_constr Σ) (pr11 X) (pr1 Y) P Q e (disp_alg_constr Y))
             (inversePathOver_PathOver_square
                (poly_dact_TotalPathToPathOver_idpath _ _))))
       (PathOver_square_id_left _)).
Qed.  

(** Now we show that a section of the projection gives rise to a dependent map to `Y` *)
Section SectionToDispAlgMap.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}
          (Y : disp_algebra X)
          (f : X --> total_algebra Y)
          (p_path : pr111 (f · projection Y) = pr111 (id₁ X))
          (pc : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
                 !(eqtohomot p_path ((pr211 X) x)) @ maponpaths pr1 ((pr121 (pr1 f)) x)
                 =
                 maponpaths (pr211 X) (! poly_pr1_is_id (pr111 f) p_path x)).
   
  Definition section_to_disp_alg_map_comp
    : ∏ x : alg_carrier X, Y x
    := transport_depmap
         (λ z, pr2 (pr111 f z))
         p_path.

  Definition section_to_disp_alg_map_constr_help
             (x : poly_act (point_constr Σ) (alg_carrier X))
    : !(maponpaths (alg_constr X) (poly_pr1_is_id (pr111 f) p_path x))
    @ !(maponpaths pr1 ((pr121 (pr1 f)) x))
    @ eqtohomot p_path ((pr211 X) x)
    =
    idpath _.
  Proof.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        refine (!_).
        apply maponpathsinv0.
      }
      exact (!(pc _)).
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0r.
    }
    apply pathsinv0l.
  Qed.    

  Definition section_to_disp_alg_map_constr
             (x : poly_act (point_constr Σ) (alg_carrier X))
    : section_to_disp_alg_map_comp (alg_constr X x)
      =
      disp_alg_constr
        Y x
        (poly_dmap
           (point_constr Σ)
           Y
           section_to_disp_alg_map_comp
           x).
  Proof.
    refine (!_).
    refine (PathOver_eq_idpath_to_path
              _
              (composePathOver
                 (inversePathOver
                    (apd_depfun
                       (poly_dact_UU (point_constr Σ) Y)
                       (pr1 Y)
                       (pr12 Y)
                       (poly_pr2_is_poly_dmap (pr111 f) p_path x)))
                 (composePathOver
                    (inversePathOver (TotalPathToPathOver ((pr121 (pr1 f)) x)))
                    (PathOver_transport
                       (eqtohomot p_path ((pr211 X) x))
                       (pr2 ((pr111 f) ((pr211 X) x))))))).
    refine (!_).
    apply section_to_disp_alg_map_constr_help.
  Defined.

  Definition inv_apd_section_endpoint_spec_index
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (alg_carrier X))
    : total_algebra.pr1_endpoint Y e (poly_map P (pr111 f) x)
    @ ! maponpaths (poly_pr1 Q) (sem_endpoint_UU_natural e (pr121 (pr1 f)) x)
    @ poly_pr1_is_id (pr111 f) p_path (sem_endpoint_UU e (pr211 X) x)
    =
    maponpaths (sem_endpoint_one_types e (pr11 X)) (poly_pr1_is_id (pr111 f) p_path x).
  Proof.
    refine (_ @ maponpaths (λ z, !z) (maponpaths_sem_endpoint_UU e f p_path pc x) @ _).
    - refine (!_).
      etrans.
      {
        apply pathscomp_inv.
      }
      etrans.
      {
        apply maponpaths.
        apply pathsinv0inv0.
      }
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp_inv.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        apply pathsinv0inv0.
      }
      exact (!(path_assoc _ _ _)).
    - etrans.
      {
        refine (!_).
        apply maponpathsinv0.
      }
      apply maponpaths.
      apply pathsinv0inv0.
  Qed.

  Definition transportf_poly_pr1_is_id
             {P : poly_code}
             (x : poly_act P (alg_carrier X))
    : transportf
        (poly_dact_UU P Y)
        (poly_pr1_is_id (pr111 f) p_path x)
        (poly_pr2 P (poly_map P (pr111 f) x))
      =
      poly_dmap P Y section_to_disp_alg_map_comp x.
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction x as [x | x].
      + exact (transportf_poly_dact_inl _ _ @ IHP₁ x).
      + exact (transportf_poly_dact_inr _ _ @ IHP₂ x).
    - exact (transportf_poly_dact_pair _ _ _ _
             @ pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
  Defined.

  Definition inv_apd_section_endpoint_id_help
             (P : poly_code)
             (x : poly_act P (alg_carrier X))
    : PathOver_square
        (poly_dact_UU
           P
           (λ x0, pr1 Y x0))
        (idpath _)
        (poly_dact_PathOver_transport
           (poly_pr1_is_id (pr111 f) p_path x)
           (poly_pr2 P (poly_map P (pr111 f) x)))
        (poly_pr2_is_poly_dmap (pr111 f) p_path x)
        (idpath _)
        (transportf_poly_pr1_is_id x
         @ endpoint_dact_natural
             (id_e (point_constr Σ) P)
             section_to_disp_alg_map_constr x).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction x as [x | x].
      + refine (@PathOver_square_1_type
                  (⟦ P₁ + P₂ ⟧ (pr111 X)) (poly_dact (P₁ + P₂) (pr1 Y))
                  _ _ _
                  _ _ _ _ _ _ _ _ _ _ _
                  (PathOver_square_path_right
                     (PathOver_square_concat
                        (poly_dact_PathOver_transport_inl _ _)
                        (PathOver_square_PathOver_inl _ _ (IHP₁ x)))
                     _)).
        simpl.
        apply path_assoc.
      + refine (@PathOver_square_1_type
                  (⟦ P₁ + P₂ ⟧ (pr111 X)) (poly_dact (P₁ + P₂) (pr1 Y))
                  _ _ _
                  _ _ _ _ _ _ _ _ _ _ _
                  (PathOver_square_path_right
                     (PathOver_square_concat
                        (poly_dact_PathOver_transport_inr _ _)
                        (PathOver_square_PathOver_inr _ _ (IHP₂ x)))
                     _)).
        simpl.
        apply path_assoc.
    - refine (@PathOver_square_1_type
                (⟦ P₁ * P₂ ⟧ (pr111 X)) (poly_dact (P₁ * P₂) (pr1 Y))
                _ _ _
                _ _ _ _ _ _ _ _ _ _ _
                (PathOver_square_path_right
                   (PathOver_square_concat
                      (poly_dact_PathOver_transport_pathsdirprod
                         (poly_pr1_is_id (pr111 f) p_path (pr1 x))
                         (poly_pr2 P₁ (poly_map P₁ (pr111 f) (pr1 x)))
                         (poly_pr1_is_id (pr111 f) p_path (pr2 x))
                         (poly_pr2 P₂ (poly_map P₂ (pr111 f) (pr2 x))))
                      (PathOver_square_PathOver_pair
                         (IHP₁ _)
                         (IHP₂ _)))
                   _)).
      simpl.
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      refine (_ @ !(pathscomp0rid _)).
      exact (paths_pathsdirprod
               (pathscomp0rid _)
               (pathscomp0rid _)).
  Qed.
    
  Definition inv_apd_section_endpoint_id
             (P : poly_code)
             (x : poly_act P (alg_carrier X))
    : PathOver_square
        (poly_dact_UU
           P
           (λ x0, pr1 Y x0))
        (idpath _)
        (composePathOver
           (identityPathOver _)
           (composePathOver
              (inversePathOver
                 (poly_dact_TotalPathToPathOver P (idpath _)))
              (poly_dact_PathOver_transport
                 (poly_pr1_is_id (pr111 f) p_path x)
                 (poly_pr2 P (poly_map P (pr111 f) x)))))
        (poly_pr2_is_poly_dmap (pr111 f) p_path x)
        (idpath _)
        (transportf_poly_pr1_is_id x
         @ endpoint_dact_natural
             (id_e (point_constr Σ) P)
             section_to_disp_alg_map_constr x).
  Proof.
    exact (PathOver_square_concat
             (PathOver_square_id_left _)
             ((@PathOver_square_1_type
                 (⟦ P ⟧ (pr111 X)) (poly_dact P (pr1 Y))
                 _ _ _
                 _ _ _ _ _ _ _ _ _ _ _
                 (PathOver_square_concat
                    (PathOver_square_comp_r
                       _
                       (inversePathOver_PathOver_square
                          (poly_dact_TotalPathToPathOver_idpath
                             P
                             (poly_map P (pr111 f) x))))
                    (PathOver_square_concat
                       (PathOver_square_id_left _)
                       (inv_apd_section_endpoint_id_help P x)))))).
  Qed.

  Definition inv_apd_section_endpoint_pair
             {P Q R : poly_code}
             {e₁ : endpoint (point_constr Σ) P Q}
             {e₂ : endpoint (point_constr Σ) P R}
             (x : poly_act P (alg_carrier X))
    : ∑ p,
      PathOver_square
        (poly_dact (Q * R) _)
        p
        (inv_apd_section_endpoint (pair e₁ e₂) f p_path x)
        (PathOver_pair
           (inv_apd_section_endpoint e₁ f p_path x)
           (inv_apd_section_endpoint e₂ f p_path x))
        (idpath _)
        (transportf_poly_dact_pair
           (poly_pr1_is_id (pr111 f) p_path (sem_endpoint_UU e₁ (pr211 X) x))
           (poly_pr1_is_id (pr111 f) p_path (sem_endpoint_UU e₂ (pr211 X) x))
           (poly_pr2 Q (poly_map Q (pr111 f) (sem_endpoint_UU e₁ (pr211 X) x)))
           (poly_pr2 R (poly_map R (pr111 f) (sem_endpoint_UU e₂ (pr211 X) x)))).
  Proof.
    refine (_ ,, _).
    apply PathOver_square_idpath_r.
    exact
      (PathOver_square_concat
         (PathOver_square_comp_l
            _
            (PathOver_square_comp_l
               _
               (poly_dact_PathOver_transport_pathsdirprod
                  (poly_pr1_is_id
                     (pr111 f)
                     p_path
                     (sem_endpoint_UU e₁ (pr211 X) x))
                  (poly_pr2
                     Q
                     (poly_map Q (pr111 f) (sem_endpoint_UU e₁ (pr211 X) x)))
                  (poly_pr1_is_id
                     (pr111 f)
                     p_path
                     (sem_endpoint_UU e₂ (pr211 X) x))
                  (poly_pr2
                     R
                     (poly_map R (pr111 f) (sem_endpoint_UU e₂ (pr211 X) x))))))
         (PathOver_square_concat
            (PathOver_square_comp_l
               _
               (PathOver_square_comp_r
                  _
                  (PathOver_square_concat
                     (inversePathOver_PathOver_square
                        (poly_dact_TotalPathToPathOver_pathsdirprod
                           (sem_endpoint_UU_natural e₁ (pr121 (pr1 f)) x)
                           (sem_endpoint_UU_natural e₂ (pr121 (pr1 f)) x)))
                     (inverse_PathOverPair _ _))))
            (PathOver_square_concat
               (PathOver_square_comp_l
                  _
                  (compose_PathOver_pair _ _ _ _))
               (compose_PathOver_pair _ _ _ _)))).
  Qed.

  Definition transportf_poly_pr1_is_id_PathOver
             (P : poly_code)
             (x : poly_act P (alg_carrier X))
    : PathOver
        (poly_dact P (pr1 Y))
        (transportf
           (poly_dact_UU P (pr1 Y))
           (poly_pr1_is_id (pr111 f) p_path x)
           (poly_pr2 P (poly_map P (pr111 f) x)))
        (poly_dmap
           P (pr1 Y)
           (transport_depmap (λ z, pr2 ((pr111 f) z)) p_path)
           x)
        (idpath _)
    := transportf_poly_pr1_is_id x.
  
  Definition poly_dact_PathOver_transport_transportf_poly_pr1_is_id_PathOver
             {P : poly_code}
             (x : poly_act P (alg_carrier X))
    : PathOver_square
        (poly_dact_UU P (pr1 Y))
        (pathscomp0rid _)
        (composePathOver
           (poly_dact_PathOver_transport
              (poly_pr1_is_id (pr111 f) p_path x)
              (poly_pr2 P (poly_map P (pr111 f) x)))
           (transportf_poly_pr1_is_id_PathOver P x))
        (poly_pr2_is_poly_dmap (pr111 f) p_path x)
        (idpath _)
        (idpath _).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply PathOver_square_id_right.
    - induction x as [x | x].
      + apply PathOver_square_idpath_r.
        refine (@PathOver_square_1_type
                 (⟦ P₁ + P₂ ⟧ (pr111 X)) (poly_dact (P₁ + P₂) (pr1 Y))
                 _ _ _
                 _ _ _ _ _ _ _ _ _ _ _
                 (PathOver_square_concat
                    _
                    (PathOver_square_PathOver_inl
                       _
                       _
                       (IHP₁ x)))).
        apply PathOver_square_idpath_r.
        refine (PathOver_square_concat
                  _
                  (PathOver_inl_compose _ _)).
        apply PathOver_square_idpath_r.
        refine (PathOver_square_concat
                  _
                  (PathOver_square_comp_r
                     _
                     (poly_dact_PathOver_transport_inl_alt _ _))).
        exact (composePathOver_assocl
                 _
                 (transportf_poly_dact_inl
                    (poly_pr1_is_id (pr111 f) p_path x)
                    (poly_pr2 P₁ (poly_map P₁ (pr111 f) x))
                  : PathOver _ _ _ (idpath _))
                 _).
      + apply PathOver_square_idpath_r.
        refine (@PathOver_square_1_type
                 (⟦ P₁ + P₂ ⟧ (pr111 X)) (poly_dact (P₁ + P₂) (pr1 Y))
                 _ _ _
                 _ _ _ _ _ _ _ _ _ _ _
                 (PathOver_square_concat
                    _
                    (PathOver_square_PathOver_inr
                       _
                       _
                       (IHP₂ x)))).
        apply PathOver_square_idpath_r.
        refine (PathOver_square_concat
                  _
                  (PathOver_inr_compose _ _)).
        apply PathOver_square_idpath_r.
        refine (PathOver_square_concat
                  _
                  (PathOver_square_comp_r
                     _
                     (poly_dact_PathOver_transport_inr_alt _ _))).
        exact (composePathOver_assocl
                 _
                 (transportf_poly_dact_inr
                    (poly_pr1_is_id (pr111 f) p_path x)
                    (poly_pr2 P₂ (poly_map P₂ (pr111 f) x))
                  : PathOver _ _ _ (idpath _))
                 _).
    - apply PathOver_square_idpath_r.
      refine (@PathOver_square_1_type
                (⟦ P₁ * P₂ ⟧ (pr111 X)) (poly_dact (P₁ * P₂) (pr1 Y))
                _ _ _
                _ _ _ _ _ _ _ _ _ _ _
                (PathOver_square_concat
                   _
                   (PathOver_square_PathOver_pair
                      (IHP₁ _)
                      (IHP₂ _)))).
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                _
                (compose_PathOver_pair _ _ _ _)).
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                _
                (PathOver_square_comp_r
                   _
                   (poly_dact_PathOver_transport_pathsdirprod_alt _ _ _ _))).
      exact (composePathOver_assocl
               _
               (transportf_poly_dact_pair
                  (poly_pr1_is_id (pr111 f) p_path (pr1 x))
                  (poly_pr1_is_id (pr111 f) p_path (pr2 x))
                  (poly_pr2 P₁ (poly_map P₁ (pr111 f) (pr1 x)))
                  (poly_pr2 P₂ (poly_map P₂ (pr111 f) (pr2 x)))
                : PathOver _ _ _ (idpath _))
               _).
  Qed.

  Definition inv_apd_section_endpoint_comp_help
             {P Q : poly_code}
             {e : endpoint (point_constr Σ) P Q}
             (x : poly_act P (alg_carrier X))
    : ∑ p,
      PathOver_square
        (poly_dact Q (pr1 Y))
        p
        (composePathOver
           (inv_apd_section_endpoint e f p_path x)
           (composePathOver
              (transportf_poly_pr1_is_id_PathOver Q (sem_endpoint_UU e (pr211 X) x))
              (inversePathOver
                 (poly_pr2_is_poly_dmap
                    (pr111 f)
                    p_path
                    (sem_endpoint_UU e (pr211 X) x)))))
        (composePathOver
           (total_algebra.pr2_endpoint Y e (poly_map P (pr111 f) x))
           (inversePathOver
              (poly_dact_TotalPathToPathOver
                 Q
                 (sem_endpoint_UU_natural e (pr121 (pr1 f)) x))))
        (idpath _)
        (idpath _).
  Proof.
    refine (_ ,, _).
    unfold inv_apd_section_endpoint.
    refine (PathOver_square_concat
              (composePathOver_assocr _ _ _)
              _).
    refine (PathOver_square_comp_l _ _).
    refine (PathOver_square_concat
              (composePathOver_assocr _ _ _)
              _).
    apply PathOver_square_idpath_r.
    refine (PathOver_square_concat
              _
              (PathOver_square_id_right _)).
    refine (PathOver_square_comp_l _ _).
    refine (PathOver_square_concat
              (composePathOver_assocl _ _ _)
              _).
    refine (@PathOver_square_move_right
              _ _ _ _ _ _ _ _ _ _ _
              (poly_pr2_is_poly_dmap
                 (pr111 f)
                 p_path
                 (sem_endpoint_UU e (pr211 X) x))
              (idpath _)
              _).
    apply poly_dact_PathOver_transport_transportf_poly_pr1_is_id_PathOver.
  Qed.
  
  Definition inv_apd_section_endpoint_comp
             {P Q R : poly_code}
             {e₁ : endpoint (point_constr Σ) P Q}
             {e₂ : endpoint (point_constr Σ) Q R}
             (x : poly_act P (alg_carrier X))
    : ∑ p,
      PathOver_square
        (poly_dact R _)
        p
        (inv_apd_section_endpoint (comp e₁ e₂) f p_path x)
        (composePathOver
           (composePathOver
              (apd_depfun
                 (poly_dact _ _)
                 (poly_dact _ _)
                 (@endpoint_dact
                    _
                    (pr11 X) (pr1 Y)
                    _ _ e₂
                    (disp_alg_constr Y))
                 (inv_apd_section_endpoint e₁ f p_path x))
              (composePathOver
                 (apd_depfun
                    (poly_dact _ _)
                    (poly_dact _ _)
                    (@endpoint_dact
                       _
                       (pr11 X) (pr1 Y)
                       _ _ e₂
                       (disp_alg_constr Y))
                    (transportf_poly_pr1_is_id_PathOver _ _))
                 (inversePathOver
                    (apd_depfun
                       (poly_dact _ _)
                       (poly_dact _ _)
                       (@endpoint_dact
                          _
                          (pr11 X) (pr1 Y)
                          _ _ e₂
                          (disp_alg_constr Y))
                       (poly_pr2_is_poly_dmap
                          (pr111 f)
                          p_path
                          (sem_endpoint_UU e₁ (pr211 X) x))))))
           (inv_apd_section_endpoint
              e₂
              f
              p_path
              (sem_endpoint_UU e₁ _ x)))
        (idpath _)
        (idpath _).
  Proof.
    refine (_ ,, _).
    refine
      (PathOver_square_concat
         (composePathOver_assocl _ _ _)
         _).
    do 2
       refine
       (PathOver_square_idpath_r
          (PathOver_square_concat
             _
             (composePathOver_assocr _ _ _))).
    refine (PathOver_square_comp_r _ _).
    refine
      (PathOver_square_concat
         (PathOver_square_comp_l
            _
            (inversePathOver_PathOver_square
               (poly_dact_TotalPathToPathOver_concat
                  _
                  (sem_endpoint_UU_natural
                     e₂
                     (pr121 (pr1 f))
                     (sem_endpoint_UU e₁ (pr211 X) x))
                  (maponpaths
                     (sem_endpoint_UU e₂ (total_algebra.operation Y))
                     (sem_endpoint_UU_natural e₁ (pr121 (pr1 f)) x)))))
         _).
    refine
      (PathOver_square_concat
         (PathOver_square_comp_l
            _
            (inversePathOver_compose _ _))
         _).
    refine
      (PathOver_square_concat
         (composePathOver_assocl _ _ _)
         _).
    refine (PathOver_square_comp_r _ _).
    refine
      (PathOver_square_concat
         (composePathOver_assocr
            (apd_depfun
               (poly_dact Q (pr1 Y))
               (poly_dact R (pr1 Y))
               (@endpoint_dact _ (pr11 X) (pr1 Y) _ _ e₂ (disp_alg_constr Y))
               (total_algebra.pr2_endpoint Y e₁ (poly_map P (pr111 f) x)))
            (total_algebra.pr2_endpoint
               Y e₂
               (sem_endpoint_UU
                  e₁
                  (total_algebra.operation Y) (poly_map P (pr111 f) x)))
            (inversePathOver
               (poly_dact_TotalPathToPathOver
                  R
                  (maponpaths
                     (sem_endpoint_UU e₂ (total_algebra.operation Y))
                     (sem_endpoint_UU_natural e₁ (pr121 (pr1 f)) x)))))
         _).
    refine (PathOver_square_concat
              (PathOver_square_comp_l
                 _
                 (pr2 (total_algebra_pr2_endpoint_natural
                         e₂
                         (sem_endpoint_UU_natural e₁ (pr121 (pr1 f)) x))))
              _).
    refine
      (PathOver_square_concat
         (composePathOver_assocl _ _ _)
         _).
    refine (PathOver_square_comp_r _ _).
    refine
      (PathOver_square_concat
         (apd_depfun_concat
            (poly_dact Q (pr1 Y)) (poly_dact R (pr1 Y))
            (@endpoint_dact
               (point_constr Σ)
               (pr11 X) (pr1 Y)
               Q R
               e₂
               (disp_alg_constr Y))
            _
            _)
         _).
    refine (inverse_PathOver_square _).
    refine
      (PathOver_square_concat
         (PathOver_square_comp_l
            _
            (PathOver_square_comp_l
               _
               (apd_depfun_inv
                  (poly_dact Q (pr1 Y)) (poly_dact R (pr1 Y))
                  (@endpoint_dact
                     (point_constr Σ)
                     (pr11 X) (pr1 Y)
                     Q R
                     e₂
                     (disp_alg_constr Y))
                  (poly_pr2_is_poly_dmap
                     (pr111 f)
                     p_path
                     (sem_endpoint_UU e₁ (pr211 X) x)))))
         _).
    refine
      (PathOver_square_concat
         (PathOver_square_comp_l
            _
            (apd_depfun_concat _ _ _ _ _))
         _).
    refine
      (PathOver_square_concat
         (apd_depfun_concat _ _ _ _ _)
         _).
    exact (apd_depfun2
             (poly_dact Q (pr1 Y)) (poly_dact R (pr1 Y))
             (@endpoint_dact
                (point_constr Σ)
                (pr11 X) (pr1 Y)
                Q R
                e₂
                (disp_alg_constr Y))
             (pr2 (inv_apd_section_endpoint_comp_help x))).
  Qed.

  Definition inv_apd_section_endpoint_spec_comp_help
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (path_alg_carrier (pr1 X)))
    : PathOver_square
        (poly_dact Q (pr1 Y))
        (idpath _)
        (apd_depfun
           (poly_dact P (pr1 Y))
           (poly_dact Q (pr1 Y))
           (@endpoint_dact (point_constr Σ) (pr11 X) (pr1 Y) _ _ e (disp_alg_constr Y))
           (transportf_poly_pr1_is_id_PathOver P x))
        (identityPathOver _)
        (idpath _)
        (!(maponpaths
             (endpoint_dact (pr11 X) (pr1 Y) e (disp_alg_constr Y))
             (transportf_poly_pr1_is_id x))).
  Proof.
    simpl.    
    apply PathOver_idpath.
  Qed.
    
  Definition inv_apd_section_endpoint_spec_help
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (alg_carrier X))
    : PathOver_square
        (poly_dact Q _)
        (inv_apd_section_endpoint_spec_index e x)
        (inv_apd_section_endpoint e f p_path x)
        (apd_depfun
           (poly_dact_UU P Y) (poly_dact Q (pr1 Y))
           (@endpoint_dact (point_constr Σ) (pr11 X) (pr1 Y) P Q e (pr12 Y))
           (poly_pr2_is_poly_dmap (pr111 f) p_path x))
        (idpath _)
        (transportf_poly_pr1_is_id _
         @ endpoint_dact_natural e section_to_disp_alg_map_constr x).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | C₁ C₂ g | ].
    - (* Identity *)
      apply PathOver_square_idpath_r.
      exact
        (@PathOver_square_1_type
           (⟦ P ⟧ (pr111 X)) (poly_dact P (pr1 Y)) _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (PathOver_square_concat
              (inv_apd_section_endpoint_id P x)
              (apd_depfun_idfun
                 (poly_pr2_is_poly_dmap (pr111 f) p_path x)))).
    - (* Composition *)
      apply PathOver_square_idpath_r.
      refine (@PathOver_square_1_type
               (⟦ R ⟧ (pr111 X)) (poly_dact R (pr1 Y))
               _ _ _
               _ _ _ _ _ _ _ _ _ _ _
               (PathOver_square_concat
                  (PathOver_square_concat
                     (pr2 (inv_apd_section_endpoint_comp _))
                     _)
                  (apd_dep_comp_fun
                     (poly_dact P _)
                     (poly_dact Q _)
                     (poly_dact R _)
                     (@endpoint_dact _ (pr11 X) (pr1 Y) _ _ e₁ (pr12 Y))
                     (@endpoint_dact _ (pr11 X) (pr1 Y) _ _ e₂ (pr12 Y))
                     (poly_pr2_is_poly_dmap (pr111 f) p_path x)))).
      refine (PathOver_square_path_right
                (PathOver_square_path_left
                   (PathOver_square_concat
                      _
                      (apd_depfun2
                         (poly_dact Q _)
                         (poly_dact R _)
                         (@endpoint_dact _ (pr11 X) (pr1 Y) _ _ e₂ (pr12 Y))
                         (IHe₁ x)))
                   (pathscomp0rid _))
                (!path_assoc _ _ _ @ _)).
      apply PathOver_square_idpath_r.
      refine
        (PathOver_square_concat
           (PathOver_square_concat
              (composePathOver_assocr _ _ _)
              (PathOver_square_comp_l
                 _
                 _))
           (PathOver_square_id_right _)).
      refine
        (PathOver_square_concat
           (composePathOver_assocr _ _ _)
           _).
      refine
        (PathOver_square_concat
           (PathOver_square_comp_l
              _
              (PathOver_square_comp_l
                 _
                 (IHe₂ _)))
           _).
      refine
        (PathOver_square_concat
           (PathOver_square_comp_l
              _
              (PathOver_square_inverse
                 (PathOver_square_inv_left _)))
           _).
      refine
        (PathOver_square_concat
           (PathOver_square_id_right _)
           (inv_apd_section_endpoint_spec_comp_help _ _)).
      simpl ; clear IHe₁ IHe₂.
      do 2 refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply maponpathsinv0.
      }
      refine (!(maponpathscomp0 _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      exact (maponpaths (λ z, z @ _) (pathsinv0l _)).
    - (* Left inclusion *)
      apply PathOver_square_idpath_r.
      exact (@PathOver_square_1_type
               (⟦ P + Q ⟧ (pr111 X)) (poly_dact (P + Q) (pr1 Y))
               _ _ _
               _ _ _ _ _ _ _ _ _ _ _
               (PathOver_square_concat
                  (inv_apd_section_endpoint_id (P + Q) (inl x))  
                  (apd_dep_inl_fun
                     (poly_pr2_is_poly_dmap (pr111 f) p_path x)))).
    - (* Right inclusion *)
      apply PathOver_square_idpath_r.
      exact (@PathOver_square_1_type
               (⟦ P + Q ⟧ (pr111 X)) (poly_dact (P + Q) (pr1 Y))
               _ _ _
               _ _ _ _ _ _ _ _ _ _ _
               (PathOver_square_concat
                  (inv_apd_section_endpoint_id (P + Q) (inr x))  
                  (apd_dep_inr_fun
                     (poly_pr2_is_poly_dmap (pr111 f) p_path x)))).
    - (* Left projection *)
      apply PathOver_square_idpath_r.
      exact (@PathOver_square_1_type
               (⟦ P ⟧ (pr111 X)) (poly_dact P (pr1 Y))
               _ _ _
               _ _ _ _ _ _ _ _ _ _ _
               (PathOver_square_concat
                  (inv_apd_section_endpoint_id P (pr1 x))
                  (apd_depfun_pr1_PathOver_pair _ _ _))).
    - (* Right projection *)
      apply PathOver_square_idpath_r.
      exact (@PathOver_square_1_type
               (⟦ Q ⟧ (pr111 X)) (poly_dact Q (pr1 Y))
               _ _ _
               _ _ _ _ _ _ _ _ _ _ _
               (PathOver_square_concat
                  (inv_apd_section_endpoint_id Q (pr2 x))
                  (apd_depfun_pr2_PathOver_pair _ _ _))).
    - (* Pairing *)
      apply PathOver_square_idpath_r.
      refine (@PathOver_square_1_type
               (⟦ Q * R ⟧ (pr111 X)) (poly_dact (Q * R) (pr1 Y))
               _ _ _
               _ _ _ _ _ _ _ _ _ _ _
               (PathOver_square_concat
                  (PathOver_square_path_right
                     (PathOver_square_concat
                        (pr2 (inv_apd_section_endpoint_pair _))
                        (PathOver_square_PathOver_pair (IHe₁ x) (IHe₂ x)))
                     (maponpaths
                        (λ z, _ @ z)
                        _
                      @ path_assoc _ _ _))
                  (apd_dep_pair_fun
                     (@endpoint_dact _ _ _ _ _ e₁ _)
                     (@endpoint_dact _ _ _ _ _ e₂ _)
                     (poly_pr2_is_poly_dmap (pr111 f) p_path x)))).
      refine (!_).
      apply pathsdirprod_concat.
    - (* Constant *)
      exact (PathOver_square_1_type
               (apd_depfun_const
                  (poly_dact_UU P Y)
                  t
                  (poly_pr2_is_poly_dmap (pr111 f) p_path x))).
    - (* Constant map *)
      use PathOver_square_1_type.
      { apply idpath. }
      apply (@PathOver_square_id
               _
               (poly_dact (C C₂) (pr1 Y))).
    - (* Constructor *)
      refine (PathOver_square_concat
                (PathOver_square_id_left _)
                _).
      use PathOver_square_move_left.
      exact (PathOver_square_1_type
               (PathOver_eq_idpath_to_path_square
                  _
                  _)).
  Qed.

  Definition inv_apd_section_endpoint_spec
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (alg_carrier X))
    : PathOver_square
        (poly_dact Q _)
        (maponpaths_sem_endpoint_UU e _ p_path pc x)
        (apd_section_endpoint e f p_path x)
        (apd_depfun
           _ (poly_dact_UU Q Y)
           (@endpoint_dact
              (point_constr Σ) (pr11 X) (pr1 Y) _ _
              e (pr12 Y))
           (inversePathOver (poly_pr2_is_poly_dmap (pr111 f) p_path x)))
        (transportf_poly_pr1_is_id _
         @ endpoint_dact_natural e section_to_disp_alg_map_constr x)
        (idpath _).
  Proof.
    apply PathOver_square_idpath_r.
    simple refine
           (@PathOver_square_1_type
              (⟦ Q ⟧ (pr111 X)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (PathOver_square_concat
                 _
                 (apd_depfun_inv _ _ _ _))).
    {
      refine (maponpaths_sem_endpoint_UU e _ p_path pc x @ maponpathsinv0 _ _).
    }
    unfold apd_section_endpoint.
    refine
      (PathOver_square_1_type
         (inverse_PathOver_square
            (PathOver_square_idpath_r
               (PathOver_square_concat
                  _
                  (PathOver_square_idpath_r
                     (PathOver_square_concat
                        (inversePathOver_compose _ _)
                        (PathOver_square_idpath_r
                           (PathOver_square_concat
                              (PathOver_square_comp_r
                                 _
                                 (inversePathOver_compose _ _))
                              (PathOver_square_idpath_r
                                 (PathOver_square_concat
                                    (composePathOver_assocr _ _ _)
                                    (PathOver_square_comp_l
                                       _
                                       (PathOver_square_comp_r
                                          _
                                          (inversePathOver_inversePathOver
                                             _))))))))))))).
    exact (inversePathOver_PathOver_square
             (PathOver_square_inverse
                (inv_apd_section_endpoint_spec_help e x))).
  Qed.

  Section Apd.
    Variable (j : path_label Σ)
             (x : poly_act (path_source Σ j) (alg_carrier X)).

    Definition apd_section_to_disp_alg_map₁
      : PathOver_square
          Y
          (idpath _)
          (apd section_to_disp_alg_map_comp (alg_path X j x))
          (PathOver_to_PathOver_transport
             p_path
             (apd (λ z, pr2 ((pr111 f) z)) (alg_path X j x)))
          (idpath _)
          (idpath _).
    Proof.
      exact (apd_transport_depmap
               (λ z, pr2 ((pr111 f) z))
               p_path
               (alg_path X j x)).
    Qed.

    Definition apd_section_to_disp_alg_map₂
      : PathOver_square
          Y
          (ap_sigma_to_apd_help (pr111 f) p_path (alg_path X j x))
          (PathOver_to_PathOver_transport
             p_path
             (apd (λ z, pr2 ((pr111 f) z)) (alg_path X j x)))
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

    Definition apd_section_to_disp_alg_map₃_help
      : ∑ p,
        PathOver_square
          Y
          p
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
      refine (_ ,, _).
      exact
        (PathOver_square_concat
           (PathTotalPathToPathOver apd_section_to_disp_alg_map₃_help_path)
           (PathOver_square_concat
              (TotalPathToPathOver_concat _ _)
              (PathOver_square_comp_l
                 _
                 (PathOver_square_concat
                    (TotalPathToPathOver_concat _ _)
                    (PathOver_square_comp_l
                       _
                       (TotalPathToPathOver_inv _)))))).
    Qed.

    Definition apd_section_to_disp_alg_map₃
      : ∑ p,
        PathOver_square
          Y
          p
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
      refine (_ ,, _).
      exact (PathOver_square_comp_l
               (inversePathOver
                  (PathOver_transport
                     (eqtohomot p_path _)
                     _))
               (PathOver_square_comp_r
                  (PathOver_transport
                     (eqtohomot p_path _)
                     _)
                  (pr2 apd_section_to_disp_alg_map₃_help))).
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
      : ∑ p,
        PathOver_square
          Y
          p
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
      refine (_ ,, _).
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                _
                (composePathOver_assocl _ _ _)).
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                _
                (composePathOver_assocl
                   (inversePathOver _)
                   (TotalPathToPathOver _)
                   (composePathOver
                      _
                      _))).
      refine (PathOver_square_comp_l _ _).
      refine (PathOver_square_concat
                (composePathOver_assocr
                   (TotalPathToPathOver _)
                   (composePathOver _ _)
                   (PathOver_transport _ _))
                _).
      refine (PathOver_square_comp_l _ _).
      unfold apd_section_to_disp_alg_map₄_right.
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                _
                (composePathOver_assocr
                   (inversePathOver _)
                   (disp_alg_path Y j _ _)
                   (composePathOver _ _))).
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                _
                (composePathOver_assocr
                   (composePathOver
                      (inversePathOver _)
                      (disp_alg_path Y j _ _))
                   _
                   (composePathOver _ _))).
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                _
                (composePathOver_assocr _ _ _)).
      refine (PathOver_square_comp_r _ _).
      refine (PathOver_square_comp_r _ _).
      unfold total_algebra.paths.
      refine (PathOver_square_concat
                (TotalPathToPathOver_PathOverToTotalPath _)
                _).
      exact (composePathOver_assocl _ _ _).
    Qed.
    
    Definition apd_section_to_disp_alg_map₅
      : PathOver_square
          Y
          (! homotsec_natural
             (alg_path X j)
             (poly_pr1_is_id (pr111 f) p_path x))
          (composePathOver
             (apd_depfun
                (poly_dact (path_source Σ j) (pr1 Y)) Y
                (@endpoint_dact
                   (point_constr Σ) (pr11 X) (pr1 Y) (path_source Σ j) I
                   (path_left Σ j) (pr12 Y))
                (inversePathOver
                   (poly_pr2_is_poly_dmap (pr111 f) p_path x)))
             (composePathOver
                (disp_alg_path
                   Y j
                   (poly_pr1
                      (path_source Σ j)
                      (poly_map (path_source Σ j) (pr111 f) x))
                   (poly_pr2
                      (path_source Σ j)
                      (poly_map (path_source Σ j) (pr111 f) x)))
                (apd_depfun
                   (poly_dact (path_source Σ j) (pr1 Y)) Y
                   (@endpoint_dact
                      (point_constr Σ) (pr11 X) (pr1 Y) 
                      (path_source Σ j) I (path_right Σ j) (pr12 Y))
                   (poly_pr2_is_poly_dmap (pr111 f) p_path x))))
          (disp_alg_path
             Y j x
             (poly_dmap
                (path_source Σ j) Y
                (transport_depmap (λ z, pr2 ((pr111 f) z)) p_path) x))
          (idpath _)
          (idpath _)
      := PathOver_natural
           (disp_alg_path Y j)
           (poly_pr2_is_poly_dmap
              (pr111 f)
              p_path
              x).

    Definition apd_section_to_disp_alg_map₆_left
      : PathOver_square
          Y
          _
          apd_section_to_disp_alg_map₄_left
          (apd_depfun
             _ Y
             (@endpoint_dact
                (point_constr Σ) (pr11 X) (pr1 Y) (path_source Σ j) I 
                (path_left Σ j) (pr12 Y))
             (inversePathOver (poly_pr2_is_poly_dmap (pr111 f) p_path x)))
          (endpoint_dact_natural (path_left Σ j) section_to_disp_alg_map_constr x)
          (idpath _)
      := PathOver_square_concat
           (composePathOver_assocr _ _ _)
           (inv_apd_section_endpoint_spec (path_left Σ j) x).

    Definition apd_section_to_disp_alg_map₆_right_inv₁
      : ∑ p,
        PathOver_square
          Y
          p
          (inversePathOver apd_section_to_disp_alg_map₄_right)
          (apd_section_endpoint (path_right Σ j) f p_path x)
          (idpath _)
          (idpath _).
    Proof.
      refine (_ ,, _).
      unfold apd_section_to_disp_alg_map₄_right, apd_section_endpoint.
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                (inversePathOver_compose _ _)
                _).
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                (PathOver_square_comp_r
                   _
                   (inversePathOver_compose _ _))
                _).
      apply PathOver_square_idpath_r.
      refine (PathOver_square_concat
                (composePathOver_assocr _ _ _)
                _).
      refine (PathOver_square_comp_l _ _).
      refine (PathOver_square_comp_r _ _).
      apply inversePathOver_inversePathOver.
    Qed.

    Definition apd_section_to_disp_alg_map₆_right_inv₂
      : ∑ p,
        PathOver_square
          Y
          p
          (apd_depfun
             _ Y
             (@endpoint_dact
                (point_constr Σ) (pr11 X) (pr1 Y) (path_source Σ j) I
                (path_right Σ j) (pr12 Y))
             (inversePathOver (poly_pr2_is_poly_dmap (pr111 f) p_path x)))
          (inversePathOver
             (apd_depfun
                _ Y
                (@endpoint_dact
                   (point_constr Σ) (pr11 X) (pr1 Y) 
                   (path_source Σ j) I (path_right Σ j) (pr12 Y))
                (poly_pr2_is_poly_dmap (pr111 f) p_path x)))
          (idpath _)
          (idpath _).
    Proof.
      refine (_ ,, _).
      apply (PathOver_square_inverse (apd_depfun_inv _ _ _ _)).
    Qed.

    Definition apd_section_to_disp_alg_map₆_right_inv
      : ∑ p,
        PathOver_square
          Y
          p
          (inversePathOver apd_section_to_disp_alg_map₄_right)
          (inversePathOver
             (apd_depfun
                _ Y
                (@endpoint_dact
                   (point_constr Σ) (pr11 X) (pr1 Y) 
                   (path_source Σ j) I (path_right Σ j) (pr12 Y))
                (poly_pr2_is_poly_dmap (pr111 f) p_path x)))   
          (endpoint_dact_natural (path_right Σ j) section_to_disp_alg_map_constr x)
          (idpath _).
    Proof.
      refine (_ ,, _).
      exact (PathOver_square_concat
               (pr2 apd_section_to_disp_alg_map₆_right_inv₁)
               (PathOver_square_idpath_r
                  (PathOver_square_concat
                     (inv_apd_section_endpoint_spec (path_right Σ j) x)
                     (pr2 apd_section_to_disp_alg_map₆_right_inv₂)))).
    Qed.
    
    Definition apd_section_to_disp_alg_map₆_right
      : ∑ p,
        PathOver_square
          Y
          p
          apd_section_to_disp_alg_map₄_right
          (apd_depfun
             _ Y
             (@endpoint_dact
                (point_constr Σ) (pr11 X) (pr1 Y) 
                (path_source Σ j) I (path_right Σ j) (pr12 Y))
             (poly_pr2_is_poly_dmap (pr111 f) p_path x))
          (idpath _)
          (endpoint_dact_natural (path_right Σ j) section_to_disp_alg_map_constr x).
    Proof.
      refine (_ ,, _).
      exact (inversePathOver_PathOver_square_inj
               (pr2 apd_section_to_disp_alg_map₆_right_inv)).
    Qed.
    
    Definition apd_section_to_disp_alg_map₆
      : PathOver_square
          Y
          _
          (composePathOver
             apd_section_to_disp_alg_map₄_left
             (composePathOver
                (disp_alg_path
                   Y j
                   (poly_pr1 _ (poly_map (path_source Σ j) (pr111 f) x))
                   (poly_pr2 _ (poly_map (path_source Σ j) (pr111 f) x)))
                apd_section_to_disp_alg_map₄_right))
          (composePathOver
             (apd_depfun
                (poly_dact (path_source Σ j) (pr1 Y)) Y
                (@endpoint_dact
                   (point_constr Σ) (pr11 X) (pr1 Y) (path_source Σ j) I
                   (path_left Σ j) (pr12 Y))
                (inversePathOver
                   (poly_pr2_is_poly_dmap (pr111 f) p_path x)))
             (composePathOver
                (disp_alg_path
                   Y j
                   (poly_pr1
                      (path_source Σ j)
                      (poly_map (path_source Σ j) (pr111 f) x))
                   (poly_pr2
                      (path_source Σ j)
                      (poly_map (path_source Σ j) (pr111 f) x)))
                (apd_depfun
                   (poly_dact (path_source Σ j) (pr1 Y)) Y
                   (@endpoint_dact
                      (point_constr Σ) (pr11 X) (pr1 Y) 
                      (path_source Σ j) I (path_right Σ j) (pr12 Y))
                   (poly_pr2_is_poly_dmap (pr111 f) p_path x))))
          (endpoint_dact_natural (path_left Σ j) section_to_disp_alg_map_constr x)
          (endpoint_dact_natural (path_right Σ j) section_to_disp_alg_map_constr x)
      := PathOver_square_conj
           (disp_alg_path
              Y j
              (poly_pr1
                 (path_source Σ j)
                 (poly_map (path_source Σ j) (pr111 f) x))
              (poly_pr2
                 (path_source Σ j)
                    (poly_map (path_source Σ j) (pr111 f) x)))
           apd_section_to_disp_alg_map₆_left
           (pr2 apd_section_to_disp_alg_map₆_right).
    
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
      exact
        (PathOver_square_1_type
           (PathOver_square_concat
              apd_section_to_disp_alg_map₂
              (PathOver_square_concat
                 (pr2 apd_section_to_disp_alg_map₃)
                 (PathOver_square_concat
                    (pr2 apd_section_to_disp_alg_map₄)
                    (PathOver_square_idpath_r
                       (PathOver_square_concat
                          apd_section_to_disp_alg_map₆
                          apd_section_to_disp_alg_map₅)))))).
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
  Defined.
End SectionToDispAlgMap.

Definition point_comp_eq
           {Σ : hit_signature}
           {X Y : hit_algebra_one_types Σ}
           {f g : X --> Y}
           (p : f = g)
           (x : poly_act (point_constr Σ) (alg_carrier X))
  : !(eqtohomot (maponpaths (λ h, pr111 h) p) (pr211 X x)) @ pr121 (pr1 f) x
    =
    pr121 (pr1 g) x
    @ maponpaths
        (λ h, (pr211 Y) (poly_map (point_constr Σ) h x))
        (!(maponpaths (λ h, pr111 h) p)).
Proof.
  induction p.
  exact (!(pathscomp0rid _)).
Qed.

Definition poly_id_poly_comp
           {P : poly_code}
           {X : one_type}
           {Y : X → one_type}
           {f : X → total2_one_type Y}
           (p : (λ x, pr1(f x)) = λ x, x)
           (x : poly_act P X)
  : poly_id P X x
    @ maponpaths (λ h, poly_map P h x) (!p)
    @ !(poly_comp P f pr1 x)
    =
    !(poly_pr1_is_id f p x).
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - refine (pathscomp0rid _ @ _).
    apply maponpaths_for_constant_function.
  - simpl.
    cbn.
    etrans.
    {
      apply pathscomp0rid.
    }
    exact (maponpathsinv0 (λ h, h x) p).
  - induction x as [x | x].
    + simpl.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (maponpathsinv0 inl).
          }
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply (maponpathscomp (λ h, poly_map P₁ h x) inl).
          }
          refine (!_).
          apply (maponpathscomp0 inl).
        }
        refine (!_).
        apply (maponpathscomp0 inl).
      }
      refine (_ @ maponpathsinv0 _ _).
      apply maponpaths.
      apply IHP₁.
    + simpl.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply (maponpathsinv0 inr).
          }
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply (maponpathscomp (λ h, poly_map P₂ h x) inr).
          }
          refine (!_).
          apply (maponpathscomp0 inr).
        }
        refine (!_).
        apply (maponpathscomp0 inr).
      }
      refine (_ @ maponpathsinv0 _ _).
      apply maponpaths.
      apply IHP₂.
  - simpl.
    unfold dirprodf_path, dirprodf.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_inv.
        }
        etrans.
        {
          apply maponpaths_2.
          exact (maponpaths_prod_path
                   (λ h, poly_map P₁ h (pr1 x))
                   (λ h, poly_map P₂ h (pr2 x))
                   (!p)).
        }
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    refine (_ @ !(pathsdirprod_inv _ _)).
    exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Section SectionOfIdToDispAlgMap.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}
          (Y : disp_algebra X)
          (f : X --> total_algebra Y)
          (p : f · projection Y = identity X).

  Definition section_to_disp_alg_map_alt_help
             (x : poly_act (point_constr Σ) (alg_carrier X))
    : !(eqtohomot
          (maponpaths
             (λ h, pr111 h) p)
          ((pr211 X) x))
    @ maponpaths pr1 (pr1 (pr211 f) x)
    @ maponpaths (pr211 X) (poly_comp (point_constr Σ) (pr111 f) pr1 x)
    =
    maponpaths (pr211 X) (poly_id (point_constr Σ) (alg_carrier X) x)
    @ maponpaths
        (λ h, (pr211 X) (poly_map (point_constr Σ) h x))
        (! maponpaths
           (λ h, pr111 h) p).
  Proof.
    refine (_ @ point_comp_eq p x).
    apply maponpaths.
    simpl.
    cbn.
    unfold homotcomp, funhomotsec, homotfun.
    simpl.
    apply maponpaths_2.
    refine (!_).
    do 2 refine (pathscomp0rid _ @ _).
    apply pathscomp0rid.
  Qed.

  Definition section_to_disp_alg_map_alt_help'
             (x : poly_act (point_constr Σ) (alg_carrier X))
    : !(eqtohomot
          (maponpaths
             (λ h, pr111 h) p)
          ((pr211 X) x))
    @ maponpaths pr1 (pr1 (pr211 f) x)
    =
    maponpaths (pr211 X) (poly_id (point_constr Σ) (alg_carrier X) x)
    @ maponpaths
        (λ h, (pr211 X) (poly_map (point_constr Σ) h x))
        (! maponpaths
           (λ h, pr111 h) p)
    @ maponpaths (pr211 X) (!(poly_comp (point_constr Σ) (pr111 f) pr1 x)).
  Proof.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpathsinv0.
    }
    refine (path_assoc _ _ _ @ _).
    use path_inv_rotate_lr.
    refine (!_).
    refine (!(path_assoc _ _ _) @ _).
    apply section_to_disp_alg_map_alt_help.
  Qed.
  
  Definition section_to_disp_alg_map_alt
    : disp_algebra_map Y.
  Proof.
    refine (section_to_disp_alg_map Y f (maponpaths (λ h, pr111 h) p) _).
    intro x.
    refine (section_to_disp_alg_map_alt_help' x @ _).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathscomp (λ h, poly_map (point_constr Σ) h x) (pr211 X)).
      }
      refine (!_).
      apply maponpathscomp0.
    }
    etrans.
    {
      refine (!_).
      apply (maponpathscomp0 (pr211 X)).
    }
    apply maponpaths.
    exact (poly_id_poly_comp _ x).
  Defined.
End SectionOfIdToDispAlgMap.
