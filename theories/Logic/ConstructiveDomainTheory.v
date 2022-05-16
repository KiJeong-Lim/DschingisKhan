Require Import Coq.Program.Basics.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Math.BasicPosetTheory.

Module BasicCoLaTheory.

  Import MathProps MathClasses BasicPosetTheory DomainTheoryHelper.

  Local Existing Instances pair_isPoset arrow_isPoset.

  Global Hint Constructors _image : poset_hints.

  Definition getInfimumOf_inCoLa {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (X : ensemble D) : {inf_X : D | isInfimumOf inf_X X} :=
    let inf_X : D := proj1_sig (getSupremumOf_inCoLa (LowerBoundsOf X)) in
    @exist D (fun inf : D => isInfimumOf inf X) inf_X (proj2 (SupremumOfLowerBounds_isInfimum inf_X X) (proj2_sig (getSupremumOf_inCoLa (LowerBoundsOf X))))
  .

  Definition MonotonicMaps (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : Type :=
    @sig (Hask.arrow dom cod) (fun f : dom -> cod => isMonotonicMap f)
  .

  Local Notation " '⟬' dom '⟶' cod '⟭' " := (MonotonicMaps dom cod) : type_scope.

  Local Instance MonotonicMaps_isPoset (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : isPoset ⟬ dom ⟶ cod ⟭ :=
    subPoset (Hask.arrow dom cod) (requiresPoset := arrow_isPoset cod_requiresPoset)
  .

  Definition supOfMonotonicMaps {dom : Type} {cod : Type} {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} {dom_requiresCoLa : isCoLa dom} {cod_requiresCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭) : dom -> cod :=
    fun x : dom => proj1_sig (getSupremumOf_inCoLa (image (fun f_i : ⟬ dom ⟶ cod ⟭ => proj1_sig f_i x) fs))
  .

  Lemma supOfMonotonicMaps_proj2_sig {dom : Type} {cod : Type} {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} {dom_requiresCoLa : isCoLa dom} {cod_requiresCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭)
    : forall x : dom, isSupremumOf (supOfMonotonicMaps fs x) (image (fun f_i : ⟬ dom ⟶ cod ⟭ => proj1_sig f_i x) fs).
  Proof. exact (fun x : dom => proj2_sig (getSupremumOf_inCoLa (image (fun f_i : ⟬ dom ⟶ cod ⟭ => proj1_sig f_i x) fs))). Qed.

  Lemma supOfMonotonicMaps_isMonotonicMap {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭)
    : isMonotonicMap (supOfMonotonicMaps fs).
  Proof.
    intros x x' x_le_x'. simpl. eapply supOfMonotonicMaps_proj2_sig with (x := x). red.
    intros y y_in. apply in_image_iff in y_in. destruct y_in as [f [y_eq f_in]]. subst y.
    transitivity (proj1_sig f x'); [eapply (proj2_sig f) | eapply supOfMonotonicMaps_proj2_sig with (x := x')]; eauto with *.
  Qed.

  Definition supremum_m {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭) : ⟬ dom ⟶ cod ⟭ :=
    @exist (dom -> cod) isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonicMap fs)
  .

  Lemma supremum_m_isSupremum {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod}
    : forall fs : ensemble ⟬ dom ⟶ cod ⟭, isSupremumOf (supremum_m fs) fs.
  Proof with eauto with *.
    unfold supremum_m; intros fs f. split; intros ?; desnw.
    - intros f_i f_i_in. rewrite <- SUPREMUM_LE_UPPER_BOUND.
      intros x. simpl. eapply supOfMonotonicMaps_proj2_sig with (x := x)...
    - intros x. simpl. eapply supOfMonotonicMaps_proj2_sig with (x := x).
      intros y y_in. apply in_image_iff in y_in. destruct y_in as [f_i [y_eq f_i_in]]. subst y.
      revert x. change (f_i =< f)...
  Qed.

  Local Instance MonotonicMaps_isCoLa (dom : Type) (cod : Type) {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod} : isCoLa ⟬ dom ⟶ cod ⟭ :=
    fun fs : ensemble ⟬ dom ⟶ cod ⟭ => @exist ⟬ dom ⟶ cod ⟭ (fun sup_fs : ⟬ dom ⟶ cod ⟭ => isSupremumOf sup_fs fs) (supremum_m fs) (supremum_m_isSupremum fs)
  .

End BasicCoLaTheory.

Module ParameterizedCoinduction.

  Import MathProps MathClasses BasicPosetTheory BasicCoLaTheory.

  Local Existing Instances pair_isPoset arrow_isPoset MonotonicMaps_isPoset MonotonicMaps_isCoLa.

End ParameterizedCoinduction.
