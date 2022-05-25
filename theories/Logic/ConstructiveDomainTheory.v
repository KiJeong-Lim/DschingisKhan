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

  Local Notation " ⟬ dom ⟶ cod ⟭ " := (MonotonicMaps dom cod) : type_scope.

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

  Lemma getLeastFixedPoint_inCoLa {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (f : D -> D)
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

  Lemma getGreatestFixedPoint_inCoLa {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (f : D -> D)
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

  Definition nu {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D (requiresPoset := requiresPoset)} (f : ⟬ D ⟶ D ⟭) : {gfp_f : D | isGreatestFixedPointOf gfp_f (proj1_sig f)} :=
    let nu_f_proj1_sig : D := proj1_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f))) in
    let IS_SUPREMUM : isSupremumOf nu_f_proj1_sig (PostfixedPoints (proj1_sig f)) := proj2_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f))) in
    @exist D (fun gfp_f : D => isGreatestFixedPointOf gfp_f (proj1_sig f)) nu_f_proj1_sig (theGreatestFixedPointOfMonotonicMap (proj1_sig f) nu_f_proj1_sig (proj2_sig f) IS_SUPREMUM)
  .

  Corollary nu_isSupremumOf_PostfixedPoints {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D (requiresPoset := requiresPoset)} (f : ⟬ D ⟶ D ⟭)
    : isSupremumOf (proj1_sig (nu f)) (PostfixedPoints (proj1_sig f)).
  Proof. exact (proj2_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f)))). Qed.

  Corollary nu_f_isGreatestFixedPointOf_f {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D (requiresPoset := requiresPoset)} (f : ⟬ D ⟶ D ⟭)
    : isGreatestFixedPointOf (proj1_sig (nu f)) (proj1_sig f).
  Proof. eapply theGreatestFixedPointOfMonotonicMap; [exact (proj2_sig f) | exact (nu_isSupremumOf_PostfixedPoints f)]. Qed.

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
    : forall x : D, x =< x1 -> x =< cola_union x1 x2.
  Proof. intros x x_le; rewrite x_le. eapply cola_union_spec; eauto with *. Qed.

  Lemma le_cola_union_intror {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, x =< x2 -> x =< cola_union x1 x2.
  Proof. intros x x_le; rewrite x_le. eapply cola_union_spec; eauto with *. Qed.

  Lemma cola_union_le_elim_l {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, cola_union x1 x2 =< x -> x1 =< x.
  Proof. intros x le_x. apply cola_union_spec in le_x. eauto with *. Qed.

  Lemma cola_union_le_elim_r {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, cola_union x1 x2 =< x -> x2 =< x.
  Proof. intros x le_x. apply cola_union_spec in le_x. eauto with *. Qed.

  Lemma cola_union_le_intro {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, x1 =< x -> x2 =< x -> cola_union x1 x2 =< x.
  Proof.
    ii; eapply cola_union_spec. intros d d_in. apply in_finite_iff in d_in.
    destruct d_in as [d_eq_x1 | [d_eq_x2 | []]]; subst d; eauto with *.
  Qed.

  Lemma cola_empty_le_intro {hasExtraColaMethods : ExtraColaMethods D}
    : forall x : D, cola_empty =< x.
  Proof.
    ii; eapply cola_empty_spec. intros d d_in. apply in_empty_iff in d_in.
    destruct d_in as [].
  Qed.

  Lemma PostfixedPoint_le_GreatestFixedPoint {requiresCoLa : isCoLa D} (f : ⟬ D ⟶ D ⟭) (x : D)
    (IS_POSTFIXEDPOINT : x =< proj1_sig f x)
    : x =< proj1_sig (nu f).
  Proof. eapply nu_isSupremumOf_PostfixedPoints; eauto with *. Qed.

  Lemma StrongCoinduction {requiresCoLa : isCoLa D} {hasExtraColaMethods : ExtraColaMethods D} (f : ⟬ D ⟶ D ⟭) (x : D)
    : x =< proj1_sig (nu f) <-> x =< proj1_sig f (cola_union x (proj1_sig (nu f))).
  Proof with eauto with *.
    assert (claim1 : proj1_sig f (proj1_sig (nu f)) =< proj1_sig f (cola_union x (proj1_sig (nu f)))).
    { eapply (proj2_sig f). eapply cola_union_spec... }
    pose proof (proj2_sig (nu f)) as [claim2 claim3]. split.
    - intros x_le. rewrite x_le at 1. transitivity (proj1_sig f (proj1_sig (nu f)))...
    - intros x_le. unnw. exploit (cola_union_le_intro x (proj1_sig (nu f)) _ x_le) as claim4.
      + do 2 red in claim2. rewrite claim2 at 1. eapply (proj2_sig f). eapply le_cola_union_intror...
      + rewrite x_le. eapply PostfixedPoint_le_GreatestFixedPoint. eapply (proj2_sig f)...
  Qed.

  Definition G_aux0 {hasExtraColaMethods : ExtraColaMethods D} (f : ⟬ D ⟶ D ⟭) (x : D) : D -> D :=
    fun y : D => proj1_sig f (cola_union x y)
  .

  Lemma G_aux0_isMonotionicMap {hasExtraColaMethods : ExtraColaMethods D} (f : ⟬ D ⟶ D ⟭) (x : D)
    : isMonotonicMap (G_aux0 f x).
  Proof.
    intros x1 x2 x1_le_x2. eapply (proj2_sig f).
    eapply cola_union_le_intro; [eapply le_cola_union_introl | rewrite x1_le_x2; eapply le_cola_union_intror]; eauto with *.
  Qed.

  Definition G_aux {hasExtraColaMethods : ExtraColaMethods D} (f : ⟬ D ⟶ D ⟭) (x : D) : ⟬ D ⟶ D ⟭ :=
    @exist (D -> D) isMonotonicMap (G_aux0 f x) (G_aux0_isMonotionicMap f x)
  .

  Context {requiresCoLa : isCoLa D} {hasExtraColaMethods : ExtraColaMethods D}.

  Definition G0 (f : ⟬ D ⟶ D ⟭) (x : D) : D := proj1_sig (nu (G_aux f x)).

  Lemma G0_isMonotionicMap (f : ⟬ D ⟶ D ⟭)
    : isMonotonicMap (G0 f).
  Proof with eauto with *.
    intros x1 x2 x1_le_x2. eapply StrongCoinduction. simpl in *.
    assert (claim1 : G0 f x1 == proj1_sig f (cola_union x1 (G0 f x1))) by eapply (proj2_sig (nu (G_aux f x1))).
    rewrite claim1 at 1. eapply (proj2_sig f). transitivity (cola_union x2 (G0 f x1)).
    - eapply cola_union_le_intro.
      + rewrite x1_le_x2 at 1. eapply le_cola_union_introl...
      + eapply le_cola_union_intror...
    - eapply cola_union_le_intro.
      + eapply le_cola_union_introl...
      + eapply le_cola_union_intror, le_cola_union_introl...
  Qed.

  Definition G1 (f : ⟬ D ⟶ D ⟭) : ⟬ D ⟶ D ⟭ := @exist (D -> D) isMonotonicMap (G0 f) (G0_isMonotionicMap f).

  Lemma G1_isMontonicMap
    : isMonotonicMap G1.
  Proof.
    intros f1 f2 f1_le_f2 x0. simpl. unfold G0.
    pose proof (nu_isSupremumOf_PostfixedPoints (G_aux f1 x0)) as claim1.
    pose proof (nu_isSupremumOf_PostfixedPoints (G_aux f2 x0)) as claim2.
    eapply claim1. ii; desnw. do 2 red in H_IN. eapply claim2; eauto with *.
    do 3 red. revert H_IN. unfold G_aux, G_aux0. simpl. intros x_le.
    rewrite x_le at 1. eapply f1_le_f2.
  Qed.

  Definition G : ⟬ ⟬ D ⟶ D ⟭ ⟶ ⟬ D ⟶ D ⟭ ⟭ :=
    @exist (⟬ D ⟶ D ⟭ -> ⟬ D ⟶ D ⟭) isMonotonicMap G1 G1_isMontonicMap
  .

  Variant ParameterizedGreatestFixedpointSpec (f : ⟬ D ⟶ D ⟭) (G_f : ⟬ D ⟶ D ⟭) : Prop :=
  | verifyParameterizedGreatestFixedpointSpec
    (INIT_COFIXPOINT : proj1_sig (nu f) == proj1_sig G_f cola_empty)
    (UNFOLD_COFIXPOINT : forall x : D, proj1_sig G_f x == proj1_sig f (cola_union x (proj1_sig G_f x)))
    (ACCUM_COFIXPOINT : forall x : D, forall y : D, y =< proj1_sig G_f x <-> y =< proj1_sig G_f (cola_union x y))
    : ParameterizedGreatestFixedpointSpec f G_f
  .

(*
  Theorem G_specification (f : ⟬ D ⟶ D ⟭)
    : ParameterizedGreatestFixedpointSpec f (proj1_sig G f).
  Proof. Admitted.

  Theorem G_characterization (f : ⟬ D ⟶ D ⟭) (G_f : ⟬ D ⟶ D ⟭)
    (G_f_spec : ParameterizedGreatestFixedpointSpec f G_f)
    : G_f == proj1_sig G f.
  Proof. Admitted.

  Theorem G_compositionality (f : ⟬ D ⟶ D ⟭) (r : D) (r1 : D) (r2 : D) (g1 : D) (g2 : D)
    (g1_le_G_f_r1 : g1 =< proj1_sig (proj1_sig G f) r1)
    (g2_le_G_f_r2 : g1 =< proj1_sig (proj1_sig G f) r2)
    (r1_le : r1 =< cola_union r g2)
    (r2_le : r2 =< cola_union r g1)
    : cola_union g1 g2 =< proj1_sig (proj1_sig G f) r.
  Proof. Admitted.
*)

  End PACO_METATHEORY.

End BasicCoLaTheory.

Module ParameterizedCoinduction.

  Import MathProps MathClasses BasicPosetTheory BasicCoLaTheory.

  Local Existing Instances pair_isPoset arrow_isPoset MonotonicMaps_isPoset MonotonicMaps_isCoLa.

End ParameterizedCoinduction.
