Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Math.BasicPosetTheory.

Module BasicCoLaTheory.

  Import MathProps MathClasses BasicPosetTheory DomainTheoryHelper.

  Local Existing Instances pair_isPoset arrow_isPoset.

  Global Hint Constructors _image _finite : poset_hints.

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

  Definition SupOfMonotonicMaps {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭) : ⟬ dom ⟶ cod ⟭ :=
    @exist (dom -> cod) isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonicMap fs)
  .

  Lemma SupOfMonotonicMaps_isSupremum {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod}
    : forall fs : ensemble ⟬ dom ⟶ cod ⟭, isSupremumOf (SupOfMonotonicMaps fs) fs.
  Proof with eauto with *.
    unfold SupOfMonotonicMaps; intros fs f. split; intros ?; desnw.
    - intros f_i f_i_in. rewrite <- SUPREMUM_LE_UPPER_BOUND.
      intros x. simpl. eapply supOfMonotonicMaps_proj2_sig with (x := x)...
    - intros x. simpl. eapply supOfMonotonicMaps_proj2_sig with (x := x).
      intros y y_in. apply in_image_iff in y_in. destruct y_in as [f_i [y_eq f_i_in]]. subst y.
      revert x. change (f_i =< f)...
  Qed.

  Local Instance MonotonicMaps_isCoLa (dom : Type) (cod : Type) {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod} : isCoLa ⟬ dom ⟶ cod ⟭ :=
    fun fs : ensemble ⟬ dom ⟶ cod ⟭ => @exist ⟬ dom ⟶ cod ⟭ (fun sup_fs : ⟬ dom ⟶ cod ⟭ => isSupremumOf sup_fs fs) (SupOfMonotonicMaps fs) (SupOfMonotonicMaps_isSupremum fs)
  .

  Lemma getLeastFixedPoint_inCoLa {D : Type} {D_isPoset : isPoset D} {D_isCoLa : isCoLa D} (f : D -> D)
    (f_isMonotonic : isMonotonicMap f)
    : {lfp_f : D | isInfimumOf lfp_f (PrefixedPoints f) /\ isLeastFixedPointOf lfp_f f}.
  Proof.
    assert (IS_INFIMUM : isInfimumOf (proj1_sig (getInfimumOf_inCoLa (PrefixedPoints f))) (PrefixedPoints f)) by exact (proj2_sig (getInfimumOf_inCoLa (PrefixedPoints f))).
    exists (proj1_sig (getInfimumOf_inCoLa (PrefixedPoints f))). split.
    - exact (IS_INFIMUM).
    - eapply theLeastFixedPointOfMonotonicMap.
      + exact (f_isMonotonic).
      + exact (IS_INFIMUM).
  Defined.

  Lemma getGreatestFixedPoint_inCoLa {D : Type} {D_isPoset : isPoset D} {D_isCoLa : isCoLa D} (f : D -> D)
    (f_isMonotonic : isMonotonicMap f)
    : {gfp_f : D | isSupremumOf gfp_f (PostfixedPoints f) /\ isGreatestFixedPointOf gfp_f f}.
  Proof.
    assert (IS_SUPREMUM : isSupremumOf (proj1_sig (getSupremumOf_inCoLa (PostfixedPoints f))) (PostfixedPoints f)) by exact (proj2_sig (getSupremumOf_inCoLa (PostfixedPoints f))).
    exists (proj1_sig (getSupremumOf_inCoLa (PostfixedPoints f))). split.
    - exact (IS_SUPREMUM).
    - eapply theGreatestFixedPointOfMonotonicMap.
      + exact (f_isMonotonic).
      + exact (IS_SUPREMUM).
  Defined.

  Definition nu {D : Type} {D_isPoset : isPoset D} {D_isCoLa : isCoLa D (requiresPoset := D_isPoset)} (f : ⟬ D ⟶ D ⟭) : {gfp_f : D | isGreatestFixedPointOf gfp_f (proj1_sig f)} :=
    let nu_proj1_sig : D := proj1_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f))) in
    let IS_SUPREMUM : isSupremumOf nu_proj1_sig (PostfixedPoints (proj1_sig f)) := proj2_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f))) in
    @exist D (fun gfp_f : D => isGreatestFixedPointOf gfp_f (proj1_sig f)) nu_proj1_sig (theGreatestFixedPointOfMonotonicMap (proj1_sig f) nu_proj1_sig (proj2_sig f) IS_SUPREMUM)
  .

  Corollary nu_isSupremumOf_PostfixedPoints {D : Type} {D_isPoset : isPoset D} {D_isCoLa : isCoLa D (requiresPoset := D_isPoset)} (f : ⟬ D ⟶ D ⟭)
    : isSupremumOf (proj1_sig (nu f)) (PostfixedPoints (proj1_sig f)).
  Proof. exact (proj2_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f)))). Qed.

  Section PACO_METATHEORY.

  Import ListNotations MathNotations.

  Class ExtraColaMethods (D : Type) {requiresPoset : isPoset D} : Type :=
    { cola_union (d_left : D) (d_right : D) : D
    ; cola_empty : D
    ; cola_union_spec (d_left : D) (d_right : D)
      : isSupremumOf (cola_union d_left d_right) (finite [d_left; d_right])
    ; cola_empty_spec
      : isSupremumOf (cola_empty) (empty)
    }
  .

  Context {D : Type} {requiresPoset : isPoset D}.

  Lemma le_cola_union_introl {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : x1 =< cola_union x1 x2.
  Proof. eapply cola_union_spec; eauto with *. Qed.

  Lemma le_cola_union_intror {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : x2 =< cola_union x1 x2.
  Proof. eapply cola_union_spec; eauto with *. Qed.

  Lemma cola_union_le_iff {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D) (x : D)
    : cola_union x1 x2 =< x <-> (x1 =< x /\ x2 =< x).
  Proof with eauto with *.
    split.
    - intros ?; split; eapply cola_union_spec...
    - intros [x1_le_x x2_le_x]. eapply cola_union_spec.
      intros d d_in. apply in_finite_iff in d_in.
      destruct d_in as [d_eq_x1 | [d_eq_x2 | []]]; subst d...
  Qed.

  Lemma cola_empty_le_intro {hasExtraColaMethods : ExtraColaMethods D} (x : D)
    : cola_empty =< x.
  Proof.
    eapply cola_empty_spec.
    intros d d_in. apply in_empty_iff in d_in.
    destruct d_in as [].
  Qed.

  End PACO_METATHEORY.

End BasicCoLaTheory.

Module ParameterizedCoinduction.

  Import MathProps MathClasses BasicPosetTheory BasicCoLaTheory.

  Local Existing Instances pair_isPoset arrow_isPoset MonotonicMaps_isPoset MonotonicMaps_isCoLa.

End ParameterizedCoinduction.
