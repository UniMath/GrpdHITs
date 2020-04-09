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
Require Import displayed_algebras.constant_display.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Definition poly_pr1_poly_map
           {P : poly_code}
           {X Y Z : one_type}
           (f : X → Y)
           (g : X → Z)
           (x : poly_act P X)
  : poly_map P f x
    =
    poly_pr1
      P
      (poly_map
         P
         (λ z, f z ,, g z)
         x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths inl (IHP₁ x)).
    + exact (maponpaths inr (IHP₂ x)).
  - exact (pathsdirprod
             (IHP₁ (pr1 x))
             (IHP₂ (pr2 x))).
Defined.






Section ProductsAlg.
  Context {Σ : hit_signature}
          (X Y : hit_algebra_one_types Σ).

  Local Notation "'P'" := (alg_carrier X × alg_carrier Y).

  Local Definition prod_point_constr
    : poly_act (point_constr Σ) P → P
    := λ x,
       alg_constr X (poly_map (point_constr Σ) (λ (z : P), pr1 z) x)
       ,,
       alg_constr Y (poly_map (point_constr Σ) (λ (z : P), pr2 z) x).

  Definition prod_prealg
    : hit_prealgebra_one_types Σ.
  Proof.
    use make_hit_prealgebra.
    - exact P.
    - abstract
        (apply isofhleveldirprod
         ; [apply (pr111 X) | apply (pr111 Y)]).
    - exact prod_point_constr.
  Defined.

  Local Definition prod_endpoint_pr1
        {Q R : poly_code}
        (e : endpoint (point_constr Σ) Q R)
        (x : poly_act Q P)
    : sem_endpoint_UU
        e
        (alg_constr X)
        (poly_map Q (λ (z : P), pr1 z) x)
      =
      poly_map
        R
        (λ (z : P), pr1 z)
        (sem_endpoint_UU e prod_point_constr x).
  Proof.
    refine (!(sem_endpoint_UU_natural
                e
                (λ (z : poly_act (point_constr Σ) P), _)
                x)).
    exact (idpath (alg_constr X _)).
  Defined.

  Local Definition prod_endpoint_pr2
        {Q R : poly_code}
        (e : endpoint (point_constr Σ) Q R)
        (x : poly_act Q P)
    : sem_endpoint_UU
        e
        (alg_constr Y)
        (poly_map Q (λ (z : P), pr2 z) x)
      =
      poly_map
        R
        (λ (z : P), pr2 z)
        (sem_endpoint_UU e prod_point_constr x).
  Proof.
    refine (!(sem_endpoint_UU_natural
                e
                (λ (z : poly_act (point_constr Σ) P), _)
                x)).
    exact (idpath _).
  Defined.

  Local Definition prod_path_constr
    :  ∏ (j : path_label Σ)
         (x : poly_act (path_source Σ j) P),
       sem_endpoint_UU (path_left Σ j) prod_point_constr x
       =
       sem_endpoint_UU (path_right Σ j) prod_point_constr x.
  Proof.
    exact (λ j x,
           pathsdirprod
             (!(prod_endpoint_pr1 _ _)
              @ alg_path X j (poly_map _ (λ (z : P), pr1 z) x)
              @ prod_endpoint_pr1 _ _)
             (!(prod_endpoint_pr2 _ _)
              @ alg_path Y j (poly_map _ (λ (z : P), pr2 z) x)
              @ prod_endpoint_pr2 _ _)).
  Defined.
    
  Definition prod_path_alg
    : hit_path_algebra_one_types Σ.
  Proof.
    use make_hit_path_algebra.
    - exact prod_prealg.
    - exact prod_path_constr.
  Defined.

  Definition prod_is_alg
    : is_hit_algebra_one_types Σ prod_path_alg.
  Proof.
    (*
    intros j x p ; simpl in j, x, p ; cbn in p.
    cbn.
    pose (alg_homot
            X j
            (poly_map (homot_point_arg Σ j) (λ (z : P), pr1 z) x)
            (prod_endpoint_pr1 _ _
             @ maponpaths (poly_map _ (λ (z : P), pr1 z)) p
             @ !(prod_endpoint_pr1 _ _))) as q.
    pose (alg_homot
            Y j
            (poly_map (homot_point_arg Σ j) (λ (z : P), pr2 z) x)
            (prod_endpoint_pr2 _ _
             @ maponpaths (poly_map _ (λ (z : P), pr2 z)) p
             @ !(prod_endpoint_pr2 _ _))) as r.
    refine (_
            @ paths_pathsdirprod
                _
                _
            @ _).
     *)
    apply TODO.
  Qed.
    
  Definition prod_alg
    : hit_algebra_one_types Σ.
  Proof.
    use make_algebra.
    - exact prod_path_alg.
    - exact prod_is_alg.
  Defined.

  Definition prod_alg_pr1
    : prod_alg --> X.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - use make_hit_prealgebra_mor.
      + exact (λ z, pr1 z).
      + intro ; apply idpath.
    - simpl.
      intros i x.
      etrans.
      {
        apply maponpaths_2.
        unfold prod_path_constr.
        exact (maponpaths_pr1_pathsdirprod _ _).
      }
      cbn.
      
        
      apply TODO.
  Defined.

  Definition prod_alg_pr2
    : prod_alg --> Y.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - use make_hit_prealgebra_mor.
      + exact (λ z, pr2 z).
      + intro ; apply idpath.
    - apply TODO.
  Defined.

  Section ProdUMPMap.
    Variable (Z : hit_algebra_one_types Σ)
             (pr1Z : Z --> X)
             (pr2Z : Z --> Y).

    Definition prod_alg_ump_1
      : Z --> prod_alg.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - use make_hit_prealgebra_mor.
        + exact (λ z, pr111 pr1Z z ,, pr111 pr2Z z).
        + simpl.
          intro.
          unfold prod_point_constr.
          use pathsdirprod.
          * refine (pr1 (pr211 pr1Z) x @ _).
            cbn.
            apply TODO.
          * refine (pr1 (pr211 pr2Z) x @ _).
            cbn.
            apply TODO.
      - simpl ; cbn.
        apply TODO.
    Defined.
    

  





Section ProductsAlg.
  Context {Σ : hit_signature}
          (X Y : hit_algebra_one_types Σ).

  Local Notation "'P'" := (alg_carrier X × alg_carrier Y).

  Definition prod_alg
    : hit_algebra_one_types Σ
    := total_algebra (const_disp_algebra X Y).

  Definition prod_alg_pr1
    : prod_alg --> X
    := projection _.

  Definition prod_alg_pr2_point_constr
             (x : poly_act (point_constr Σ) P)
    : prealg_constr
        (poly_dact_const
           (point_constr Σ)
           (poly_pr1 (point_constr Σ) x)
           (poly_pr2 (point_constr Σ) x))
      =
      prealg_constr
        (poly_map
           (point_constr Σ)
           (λ z : P, pr2 z)
           x).
  Proof.
    apply TODO.
  Defined.

  Definition prod_alg_pr2_path_constr_type
             (i : path_label Σ)
             (x : poly_act (path_source Σ i) P)
    : UU.
  Proof.
    refine
      (maponpaths
        (λ z : P, pr2 z)
        (total_algebra.paths (const_disp_algebra X Y) i x)
      @ sem_endpoint_UU_natural (path_right Σ i) prod_alg_pr2_point_constr x
      =
      sem_endpoint_UU_natural (path_left Σ i) prod_alg_pr2_point_constr x
      @ _).
    exact (alg_path Y i (poly_map (path_source Σ i) (λ (z : P), pr2 z) x)).
  Defined.

  Definition prod_alg_pr2_path_constr
             (i : path_label Σ)
             (x : poly_act (path_source Σ i) P)
    : prod_alg_pr2_path_constr_type i x.
  Proof.
    unfold prod_alg_pr2_path_constr_type.
    apply TODO.
  Qed.

  Definition prod_alg_pr2
    : prod_alg --> Y.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - use make_hit_prealgebra_mor.
      + exact (λ z, pr2 z).
      + exact prod_alg_pr2_point_constr.
    - exact prod_alg_pr2_path_constr.
  Defined.
  
  Section ProdUMPMap.
    Variable (Z : hit_algebra_one_types Σ)
             (pr1Z : Z --> X)
             (pr2Z : Z --> Y).

    Definition prod_alg_ump_1
      : Z --> prod_alg.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - use make_hit_prealgebra_mor.
        + exact (λ z, pr111 pr1Z z ,, pr111 pr2Z z).
        + simpl.
          cbn.
          unfold total_algebra.operation.
          simpl.
          cbn.
          unfold const_disp_algebra_constr.
          intro.
          use pathsdirprod.
          * pose (pr1 (pr211 pr1Z)) as p.
            cbn in p.
            refine (p _ @ _).
            apply maponpaths.
            exact (poly_pr1_poly_map (pr111 pr1Z) (pr111 pr2Z) x).
          * pose (pr1 (pr211 pr2Z)) as p.
            cbn in p.
            refine (p _ @ _).
            apply maponpaths.
            apply TODO.
      - apply TODO.
    Defined.

    Definition prod_alg_ump_1_pr1
      : prod_alg_ump_1 · prod_alg_pr1
        ==>
        pr1Z.
    Proof.
      simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
      - intro x ; apply idpath.
      - (*
        use funextsec.
        intro z ; cbn.
        unfold homotcomp, homotfun, funhomotsec ; cbn.
        rewrite !pathscomp0rid.
         *)
        apply TODO.
    Defined.

    Definition prod_alg_ump_1_pr2
      : prod_alg_ump_1 · prod_alg_pr2
        ==>
        pr2Z.
    Proof.
      simple refine (((_ ,, _) ,, λ _, tt) ,, tt).
      - intro x ; apply idpath.
      - (*
        use funextsec.
        intro z ; cbn.
        unfold homotcomp, homotfun, funhomotsec ; cbn.
        rewrite !pathscomp0rid.
         *)
        apply TODO.
    Defined.
  End ProdUMPMap.
End ProductsAlg.
