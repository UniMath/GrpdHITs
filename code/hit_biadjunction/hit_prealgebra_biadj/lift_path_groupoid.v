(* Lifting pseudofunctors to pseudofunctors on algebras *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.

Local Open Scope cat.

Local Arguments poly_act_functor_composition_data _ {_ _ _} _ _.
Local Arguments poly_act_nat_trans_data _ {_ _ _ _} _.

Section LiftPseudofunctor.
  Variable (P : poly_code).

  Definition prealg_path_groupoid_map
             (X : one_type)
    : (disp_alg_bicat (⟦ P ⟧)) X → (disp_alg_bicat ⦃ P ⦄) (path_groupoid X)
    := λ f, poly_path_groupoid P X ∙ #path_groupoid f.

  Definition prealg_path_groupoid_mor_comp
             {X Y : one_type}
             {f : X → Y}
             {hX : (disp_alg_bicat (⟦ P ⟧)) X}
             {hY : (disp_alg_bicat (⟦ P ⟧)) Y}
             (hf : hX -->[ f] hY)
             (z : (⦃ P ⦄ (path_groupoid X) : groupoid))
    : f (hX (pr1 (pr111 (poly_path_groupoid P) X) z))
      =
      hY (pr1 ( pr111 (poly_path_groupoid P) Y) (poly_map P f z))
    := pr1 hf (pr1 (poly_path_groupoid P X) z)
           @ maponpaths hY (pr11 (psnaturality_of (poly_path_groupoid P) f) z).

  Definition prealg_path_groupoid_mor_is_nat_trans
             {X Y : one_type}
             {f : X → Y}
             {hX : (disp_alg_bicat (⟦ P ⟧)) X}
             {hY : (disp_alg_bicat (⟦ P ⟧)) Y}
             (hf : hX -->[ f] hY)            
    : is_nat_trans
        (prealg_path_groupoid_map X hX ∙ # path_groupoid f)
        (# ⦃ P ⦄ (# path_groupoid f) ∙ prealg_path_groupoid_map Y hY)
        (prealg_path_groupoid_mor_comp hf).
  Proof.
    intros x y g.
    etrans.
    {
      refine (maponpaths (λ z, _ @ (z @ _)) _).
      exact (homotsec_natural
               (pr1 hf)
               (# (poly_path_groupoid P X : _ ⟶ _) g)).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp hX f _).
      }
      refine (!(maponpathscomp0 (f ∘ hX)%functions _ _) @ _).
      apply maponpaths.
      apply pathsinv0r.
    }
    etrans.
    {
      apply maponpaths_2.
      apply pathscomp0lid.
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (maponpathscomp _ hY).
    }
    refine (!(maponpathscomp0 hY _ _) @ _ @ maponpathscomp0 _ _ _).
    apply maponpaths.
    exact (pr21 (psnaturality_of (poly_path_groupoid P) f) _ _ g).
  Qed.
 
  Definition prealg_path_groupoid_mor
             {X Y : one_type}
             {f : X → Y}
             {hX : (disp_alg_bicat (⟦ P ⟧)) X}
             {hY : (disp_alg_bicat (⟦ P ⟧)) Y}
             (hf : hX -->[ f] hY)
    : (prealg_path_groupoid_map X hX ∙ # path_groupoid f)
      ⟹
      # ⦃ P ⦄ (# path_groupoid f) ∙ prealg_path_groupoid_map Y hY.
  Proof.
    use make_nat_trans.
    - exact (prealg_path_groupoid_mor_comp hf).
    - exact (prealg_path_groupoid_mor_is_nat_trans hf).
  Defined.

  Definition prealg_path_groupoid_cell_help
             {X Y : one_types}
             {f g : one_types ⟦ X, Y ⟧}
             (p : f ==> g)
             (z : poly_act P (X : one_type))
    : ! poly_homot P p ((pr1 ((poly_path_groupoid P) X)) z)
    @ (pr11 (psnaturality_of (poly_path_groupoid P) f)) z
    @ # (poly_path_groupoid P Y : _ ⟶ _)
          (poly_act_nat_trans_data
             P
             (path_to_nattrans p) z)
    =
    (pr11 (psnaturality_of (poly_path_groupoid P) g)) z.
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (idpath (idpath z)).
    - apply pathsinv0l.
    - induction z as [z | z].
      + simpl.
        etrans.
        {
          apply maponpaths_2.
          exact (!(maponpathsinv0 inl _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathscomp0 inl _ _)).
        }
        refine (!(maponpathscomp0 inl _ _) @ _).
        apply maponpaths.
        exact (IHP₁ z).
      + simpl.
        etrans.
        {
          apply maponpaths_2.
          exact (!(maponpathsinv0 inr _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathscomp0 inr _ _)).
        }
        refine (!(maponpathscomp0 inr _ _) @ _).
        apply maponpaths.
        exact (IHP₂ z).
    - simpl.
      etrans.
      {
        apply maponpaths_2.
        apply pathsdirprod_inv.
      }
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_concat.
      }
      refine (pathsdirprod_concat _ _ _ _ @ _).
      exact (maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
             @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
  Qed.

  Definition prealg_path_groupoid_cell
             {X Y : one_types}
             {f g : one_types ⟦ X, Y ⟧}
             {p : f ==> g}
             {hX : (disp_alg_bicat (⟦ P ⟧)) X}
             {hY : (disp_alg_bicat (⟦ P ⟧)) Y}
             {hf : hX -->[ f] hY}
             {hg : hX -->[ g] hY}
             (hp : hf ==>[ p] hg)
             (z : (⦃ P ⦄ (path_groupoid X) : groupoid))
    : p (hX (pr1 (pr111 (poly_path_groupoid P) X) z))
    @ prealg_path_groupoid_mor_comp hg z
    =
    prealg_path_groupoid_mor_comp hf z
    @ maponpaths hY
        (# (poly_path_groupoid P Y : _ ⟶ _)
           (poly_act_nat_trans_data
              P (path_to_nattrans p) z)).
  Proof.
    simpl.
    unfold prealg_path_groupoid_mor_comp.
    refine (!_).
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      exact (!(maponpathscomp0 hY _ _)).
    }
    assert
    (pr1 hf ((pr1 ((poly_path_groupoid P) X)) z)
     =
     p (hX ((pr1 ((pr111 (poly_path_groupoid P)) X)) z)) @
       pr1 hg ((pr1 ((poly_path_groupoid P) X)) z)
     @ maponpaths
         hY
         (!(poly_homot P p ((pr1 ((poly_path_groupoid P) X)) z))))
      as H.
    {
      refine (!_).
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        exact (eqtohomot hp ((pr1 ((poly_path_groupoid P) X)) z)).
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (!(maponpathscomp0 hY _ _) @ _).
        apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
    }
    etrans.
    {
      apply maponpaths_2.
      exact H.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!(maponpathscomp0 hY _ _) @ _).
    apply maponpaths.
    exact (prealg_path_groupoid_cell_help p z).
  Qed.

  Definition prealg_path_groupoid_identitor
             {X : one_type}
             (XX : (disp_alg_bicat (⟦ P ⟧)) X)
             (z : (⦃ P ⦄ (path_groupoid X) : groupoid))
    : maponpaths
        XX
        (poly_id P X ((pr1 ((poly_path_groupoid P) X)) z))
    @ maponpaths
        XX
        ((pr11 (psnaturality_of (poly_path_groupoid P) (λ x : X, x))) z)
    =
    maponpaths
      XX
      (# (poly_path_groupoid P X : _ ⟶ _)
         (poly_act_functor_identity_data P (one_type_to_groupoid X) z))
    @ maponpaths
        XX
        (# (poly_path_groupoid P X : _ ⟶ _)
           (poly_act_nat_trans_data
              P  (path_groupoid_identitor X) z)).
  Proof.
    refine (!(maponpathscomp0 XX _ _) @ _ @ maponpathscomp0 XX _ _).
    apply maponpaths.
    clear XX.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - exact (idpath (idpath z)).
    - exact (idpath (idpath z)).
    - induction z as [z | z].
      + exact (!(maponpathscomp0 inl _ _)
                @ maponpaths (maponpaths inl) (IHP₁ z)
                @ maponpathscomp0 inl _ _).
      + exact (!(maponpathscomp0 inr _ _)
                @ maponpaths (maponpaths inr) (IHP₂ z)
                @ maponpathscomp0 inr _ _).
    - exact (pathsdirprod_concat _ _ _ _
              @ maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
              @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))
              @ !(pathsdirprod_concat _ _ _ _)).
  Qed.

  Definition prealg_mor_inv
             {X Y : one_types}
             {f : one_types ⟦ X, Y ⟧}
             {hX : (disp_alg_bicat (⟦ P ⟧)) X}
             {hY : (disp_alg_bicat (⟦ P ⟧)) Y}
             (hf : hX -->[ f] hY)
    : prealg_path_groupoid_map X hX
      -->[ # path_groupoid f]
      prealg_path_groupoid_map Y hY.
  Proof.
    use make_invertible_2cell.
    - exact (prealg_path_groupoid_mor hf).
    - apply grpd_bicat_is_invertible_2cell.
  Defined.

  Definition prealg_path_groupoid_compositor_lemma
             {X Y Z : one_types}
             (f : one_types ⟦ X, Y ⟧)
             (g : one_types ⟦ Y, Z ⟧)
             (z : poly_act P (X : one_type))
    : maponpaths
        (# (⟦ P ⟧) g)
        ((pr11 (psnaturality_of (poly_path_groupoid P) f)) z)
     @ (pr11 (psnaturality_of (poly_path_groupoid P) g)) (poly_map P f z)
     @ # (poly_path_groupoid P Z : _ ⟶ _)
           (poly_act_functor_composition_data
              P
              (function_to_functor f) (function_to_functor g) z)
      @ # (poly_path_groupoid P Z : _ ⟶ _)
           (poly_act_nat_trans_data P (path_groupoid_compositor f g) z)
      =
      poly_comp P f g ((pr1 ((poly_path_groupoid P) X)) z)
      @ (pr11 (psnaturality_of (poly_path_groupoid P) (λ x, g (f x)))) z.
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (idpath (idpath z)).
    - exact (idpath (idpath (g(f z)))).
    - induction z as [z | z].
      + simpl.
        refine (_ @ maponpathscomp0 inl _ _).
        etrans.
        {
          apply maponpaths_2.
          apply coprodf_path_maponpaths_inl.
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp0 inl _ _)).
          }
          exact (!(maponpathscomp0 inl _ _)).
        }
        refine (!(maponpathscomp0 inl _ _) @ _).
        exact (maponpaths (maponpaths inl) (IHP₁ z)).
      + simpl.
        refine (_ @ maponpathscomp0 inr _ _).
        etrans.
        {
          apply maponpaths_2.
          apply coprodf_path_maponpaths_inr.
        }
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp0 inr _ _)).
          }
          exact (!(maponpathscomp0 inr _ _)).
        }
        refine (!(maponpathscomp0 inr _ _) @ _).
        exact (maponpaths (maponpaths inr) (IHP₂ z)).
    - simpl.
      refine (_ @ !(pathsdirprod_concat _ _ _ _)).
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpaths_pathsdirprod _ _ _ _)).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      refine (pathsdirprod_concat _ _ _ _ @ _).
      exact (maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
             @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
  Qed.                        
  
  Definition prealg_path_groupoid_compositor_equation
             {X Y Z : one_types}
             {f : one_types ⟦ X, Y ⟧}
             {g : one_types ⟦ Y, Z ⟧}
             {hX : (disp_alg_bicat (⟦ P ⟧)) X}
             {hY : (disp_alg_bicat (⟦ P ⟧)) Y}
             {hZ : (disp_alg_bicat (⟦ P ⟧)) Z}
             (hf : hX -->[ f] hY)
             (hg : hY -->[ g] hZ)
             (z : poly_act P (X : one_type))
    : ((maponpaths g (prealg_path_groupoid_mor_comp hf z)
    @ prealg_path_groupoid_mor_comp hg (poly_map P f z))
    @ maponpaths hZ
        (# (poly_path_groupoid P Z : _ ⟶ _)
           (poly_act_functor_composition_data
              P
              (function_to_functor f)
              (function_to_functor g) z)))
    @ maponpaths hZ
        (# (poly_path_groupoid P Z : _ ⟶ _)
           (poly_act_nat_trans_data
              P
              (path_groupoid_compositor f g) z))
    =
    ((maponpaths g (pr1 hf ((pr1 ((poly_path_groupoid P) X)) z))
    @ pr1 hg (poly_map P f ((pr1 ((poly_path_groupoid P) X)) z)))
    @ maponpaths hZ
        (poly_comp P f g ((pr1 ((poly_path_groupoid P) X)) z)))
    @ maponpaths hZ
        ((pr11 (psnaturality_of (poly_path_groupoid P) (λ x, g (f x)))) z).
  Proof.
    refine (!_).
    do 2 refine (!(path_assoc _ _ _) @ _).
    do 2 refine (_ @ path_assoc _ _ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp0 hZ _ _)).
      }
      exact (!(maponpathscomp0 hZ _ _)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathscomp0 hZ _ _)).
    }
    refine (!_).
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply (maponpathscomp hY g).
      }
      exact (homotsec_natural'
               (pr1 hg)
               (pr11 (psnaturality_of (poly_path_groupoid P) f) z)).
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp _ hZ _)).
    }
    refine (!(maponpathscomp0 hZ _ _) @ _).
    apply maponpaths.
    exact (prealg_path_groupoid_compositor_lemma f g z).
  Qed.
  
  Definition prealg_path_groupoid_compositor
             {X Y Z : one_types}
             {f : one_types ⟦ X, Y ⟧}
             {g : one_types ⟦ Y, Z ⟧}
             {hX : (disp_alg_bicat (⟦ P ⟧)) X}
             {hY : (disp_alg_bicat (⟦ P ⟧)) Y}
             {hZ : (disp_alg_bicat (⟦ P ⟧)) Z}
             (hf : hX -->[ f] hY)
             (hg : hY -->[ g] hZ)
    : alg_disp_cat_2cell
        ⦃ P ⦄
        _ _ _ _
        (psfunctor_comp path_groupoid f g)
        _ _
        (prealg_mor_inv hf;; prealg_mor_inv hg)%mor_disp
        (prealg_mor_inv (hf;; hg)).
  Proof.
    use nat_trans_eq.
    { apply homset_property. }
    intros z.
    etrans.
    {
      refine (maponpaths (λ z, (z @ _) @ _) _).
      refine (pathscomp0rid _ @ _).
      refine (maponpaths (λ z, z @ _) _).
      apply pathscomp0rid.
    }
    refine (!_).
    etrans.
    {
      refine (maponpaths (λ z, (z @ _) @ _) _).
      refine (pathscomp0rid
                ((maponpaths
                    g
                    (prealg_path_groupoid_mor_comp hf z)
                  @ idpath _)
                  @  prealg_path_groupoid_mor_comp hg (poly_map P f z))
                @ _).
      refine (maponpaths (λ z, z @ _) _).
      apply pathscomp0rid.    
    }
    exact (prealg_path_groupoid_compositor_equation hf hg z).
  Qed.

  Definition prealg_path_groupoid
    : disp_psfunctor
        (disp_alg_bicat (⟦ P ⟧))
        (disp_alg_bicat ⦃ P ⦄) path_groupoid.
  Proof.
    use make_disp_psfunctor.
    - apply disp_2cells_isaprop_alg.
    - apply disp_locally_groupoid_alg.
    - exact prealg_path_groupoid_map.
    - exact @prealg_mor_inv.
    - abstract
        (intros X Y f g p hX hY hf hg hp ;
         use nat_trans_eq ;
         [ apply homset_property
         | exact (prealg_path_groupoid_cell hp) ]).
    - abstract
        (intros X XX ;
         use nat_trans_eq ;
         [ apply homset_property
         | exact (prealg_path_groupoid_identitor XX)]).
    - exact @prealg_path_groupoid_compositor.
  Defined.
End LiftPseudofunctor.
