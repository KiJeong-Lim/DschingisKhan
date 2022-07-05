Require Import Coq.Lists.List.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeClassic.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BasicGeneralTopology.
Require Import DschingisKhan.Logic.ScottTopology.

Module BasicCpoTheory.

  Import ListNotations MathProps MathClasses BasicPosetTheory BasicGeneralTopology DomainTheoryHelper ScottTopology ExclusiveMiddle.

(* "2022-07-06: REFACTOR ME!"

  Definition ScottContinuousMaps (D1 : Type) (D2 : Type) {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} : Type :=
    @sig (Hask.arrow D1 D2) (isContinuousMap (dom_isTopology := TopologyOfDanaScott D1) (cod_isTopology := TopologyOfDanaScott D2))
  .

  Global Instance ScottContinuousMaps_asPoset (D1 : Type) (D2 : Type) {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} : isPoset (ScottContinuousMaps D1 D2) :=
    @subPoset (Hask.arrow D1 D2) (@arrow_isPoset D1 D2 D2_isPoset) (isContinuousMap (dom_isTopology := TopologyOfDanaScott D1) (cod_isTopology := TopologyOfDanaScott D2))
  .

  Local Notation " ⟬ D1 ⟶ D2 ⟭ " := (ScottContinuousMaps D1 D2) : type_scope.

  Definition U {D : Type} {D_isPoset : isPoset D} (x : D) : ensemble D :=
    fun z : D => ~ z =< x
  .

  Lemma U_x_isOpen {D : Type} {D_isPoset : isPoset D} (x : D)
    : isOpen (U x).
  Proof. (* Thanks to Junyoung Jang *)
    split.
    - intros y z y_in_U_x y_le_z z_le_x. unnw. contradiction y_in_U_x. now transitivity (z).
    - intros X [X_nonempty DIRECTED_OR_EMPTY] sup_X sup_X_isSupremumOf_X sup_X_in_U_x; unnw.
      assert (NOT_UPPER_BOUND : ~ member x (UpperBoundsOf X)).
      { ii; desnw. contradiction sup_X_in_U_x. now eapply sup_X_isSupremumOf_X. }
      eapply NNPP. intros H_false. contradiction NOT_UPPER_BOUND. intros y y_in_X.
      eapply NNPP. intros y_in_U_x. contradiction H_false. now exists (y).
  Qed.

  Lemma ScottContinuousMap_isMonotonicMap {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} (f : D1 -> D2)
    (f_isContinuousMap : isContinuousMap f)
    : isMonotonicMap f.
  Proof.
    intros x1 x2 x1_le_x2. eapply NNPP. intros f_x1_in_U_f_x2.
    assert (x1_in_preimage_f_U_f_x2 : member x1 (preimage f (U (f x2)))) by now econstructor.
    assert (preimage_f_U_f_x2_isOpen : isOpen (preimage f (U (f x2)))) by eapply f_isContinuousMap, U_x_isOpen.
    assert (x2_in_preimage_f_U_f_x2 : member x2 (preimage f (U (f x2)))).
    { inversion preimage_f_U_f_x2_isOpen. eapply UPWARD_CLOSED with (x := x1); eauto. }
    assert (f_x2_in_U_f_x2 : member (f x2) (U (f x2))) by now inversion x2_in_preimage_f_U_f_x2; subst.
    now contradiction f_x2_in_U_f_x2.
  Qed.

  Global Hint Resolve ScottContinuousMap_isMonotonicMap : poset_hints.

  Lemma f_sup_X_eq_sup_image_f_X {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (f : D1 -> D2) (X : ensemble D1) (sup_X : D1)
    (f_isContinuousMap : isContinuousMap f)
    (X_isDirected : isDirected X)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    (image_f_X_isDirected : isDirected (image f X))
    : f sup_X == proj1_sig (getSupremumOf_inCPO (image f X) image_f_X_isDirected).
  Proof with eauto with *.
    assert (f_isMonotonicMap : isMonotonicMap f) by now eapply ScottContinuousMap_isMonotonicMap.
    revert image_f_X_isDirected. keep (image f X) as Y into (ensemble D2). fold Y. ii.
    destruct (getSupremumOf_inCPO Y image_f_X_isDirected) as [sup_Y sup_Y_isSupremumOf_Y]; simpl.
    assert (claim1 : sup_Y =< f sup_X).
    { eapply sup_Y_isSupremumOf_Y. intros y y_in_Y. unnw.
      apply in_image_iff in y_in_Y. des.
      eapply f_isMonotonicMap, sup_X_isSupremumOf_X...
    }
    assert (claim2 : f sup_X =< sup_Y).
    { eapply NNPP. intros f_sup_X_in_U_sup_Y.
      assert (sup_X_in_preimage_f_U_sup_Y : member sup_X (preimage f (U sup_Y))) by now constructor.
      assert (f_U_sup_Y_isOpen : isOpen (preimage f (U sup_Y))) by now eapply f_isContinuousMap, U_x_isOpen.
      inversion f_U_sup_Y_isOpen. pose proof (LIMIT X X_isDirected sup_X sup_X_isSupremumOf_X sup_X_in_preimage_f_U_sup_Y) as [x1 [x1_in_X x1_in_preimage_f_U_sup_Y]].
      assert (f_x1_in_image_f_X : member (f x1) (image f X)).
      { econstructor... }
      assert (f_x1_in_U_sup_Y : member (f x1) (U sup_Y)).
      { apply in_preimage_iff in x1_in_preimage_f_U_sup_Y. des... }
      contradiction f_x1_in_U_sup_Y. eapply sup_Y_isSupremumOf_Y...
    }
    eapply @leProp_Antisymmetric with (requiresPoset := D2_isPoset)...
  Qed.

  Lemma sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (f : D1 -> D2) (X : ensemble D1) (sup_X : D1) (sup_Y : D2)
    (f_isContinuousMap : isContinuousMap f)
    (X_isDirected : isDirected X)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : isSupremumOf sup_Y (image f X) <-> f sup_X == sup_Y.
  Proof.
    assert (image_f_X_isDirected : isDirected (image f X)).
    { eapply preservesDirected_if_isMonotonicMap; eauto with *. }
    split.
    - intros sup_Y_isSupremumOf_image_f_X.
      rewrite f_sup_X_eq_sup_image_f_X with (f := f) (f_isContinuousMap := f_isContinuousMap) (X_isDirected := X_isDirected) (sup_X_isSupremumOf_X := sup_X_isSupremumOf_X) (image_f_X_isDirected := image_f_X_isDirected).
      eapply Supremum_preserves_eqProp_wrtEnsembles.
      + exact (proj2_sig (getSupremumOf_inCPO (image f X) image_f_X_isDirected)).
      + exact (sup_Y_isSupremumOf_image_f_X).
      + reflexivity.
    - intros f_sup_X_eq_sup_Y. rewrite <- f_sup_X_eq_sup_Y.
      rewrite f_sup_X_eq_sup_image_f_X with (f := f) (f_isContinuousMap := f_isContinuousMap) (X_isDirected := X_isDirected) (sup_X_isSupremumOf_X := sup_X_isSupremumOf_X) (image_f_X_isDirected := image_f_X_isDirected).
      exact (proj2_sig (getSupremumOf_inCPO (image f X) image_f_X_isDirected)).
  Qed.

  Corollary ScottContinuousMap_preservesSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (f : D1 -> D2) (X : ensemble D1) (sup_X : D1)
    (f_isContinuousMap : isContinuousMap f)
    (X_isDirected : isDirected X)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : isSupremumOf (f sup_X) (image f X).
  Proof. eapply sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y; eauto with *. Qed.

  Definition preservesSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} (f : D1 -> D2) : Prop :=
    forall X : ensemble D1, ⟪ DIRECTED : isDirected X ⟫ -> exists sup_X : D1, exists sup_Y : D2, isSupremumOf sup_X X /\ isSupremumOf sup_Y (image f X) /\ f sup_X == sup_Y
  .

  Lemma isMonotonicMap_if_preservesSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (f : D1 -> D2)
    (f_preserves_eqProp : preserves_eqProp1 f)
    (f_preservesSupremum : preservesSupremum f)
    : isMonotonicMap f.
  Proof.
    intros x1 x2 x1_le_x2. keep (finite [x1; x2]) as X into (ensemble D1). keep (image f X) as Y into (ensemble D2).
    assert (claim1 : isSupremumOf x2 X).
    { intros z. split; unnw.
      - intros x2_le_z x x_in_X. apply in_finite_iff in x_in_X.
        destruct x_in_X as [x_eq_x1 | [x_eq_x2 | []]]; subst x.
        + etransitivity; eauto.
        + eauto.
      - intros z_isUpperBoundOf_X. eapply z_isUpperBoundOf_X.
        eapply in_finite_iff; right; left; reflexivity.
    }
    assert (X_isDirected : isDirected X).
    { split.
      - exists (x1). eapply in_finite_iff. left. reflexivity.
      - intros z1 ? z2 ?; desnw. apply in_finite_iff in H_IN1, H_IN2.
        destruct H_IN1 as [z1_eq_x1 | [z1_eq_x2 | []]], H_IN2 as [z2_eq_x1 | [z2_eq_x2 | []]]; subst z1 z2.
        all: exists (x2); split; [eapply in_finite_iff; right; left; reflexivity | split; eauto with *].
    }
    pose proof (f_preservesSupremum X X_isDirected) as [sup_X [sup_Y [sup_X_isSupremumOf_X [sup_Y_isSupremumOf_Y f_sup_X_eq_sup_Y]]]].
    assert (it_is_sufficient_to_show : f sup_X == f x2).
    { eapply f_preserves_eqProp. eapply Supremum_preserves_eqProp_wrtEnsembles; eauto with *. }
    transitivity (sup_Y).
    - rewrite <- f_sup_X_eq_sup_Y. eapply sup_Y_isSupremumOf_Y; eauto with *.
    - rewrite <- f_sup_X_eq_sup_Y. now eapply eqProp_implies_leProp.
  Qed.

  Lemma liftsDirected_if_preservesSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (f : D1 -> D2)
    (f_preserves_eqProp : preserves_eqProp1 f)
    (f_preservesSupremum : preservesSupremum f)
    : forall X : ensemble D1, << DIRECTED : isDirected X >> -> isDirected (image f X).
  Proof with eauto with *.
    pose proof (isMonotonicMap_if_preservesSupremum f f_preserves_eqProp f_preservesSupremum) as claim1.
    ii; desnw. inversion DIRECTED. desnw. split.
    - exists (f x0)...
    - intros y1 ? y2 ?; desnw. apply in_image_iff in H_IN1, H_IN2.
      destruct H_IN1 as [x1 [y1_eq_f_x1 x1_in_X]], H_IN2 as [x2 [y1_eq_f_x2 x2_in_X]]; subst y1 y2.
      pose proof (DIRECTED_OR_EMPTY x1 x1_in_X x2 x2_in_X) as [x3 [x3_in_X [? ?]]]; unnw.
      exists (f x3); split...
  Qed.

  Theorem the_main_reason_for_introducing_ScottTopology {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (f : D1 -> D2)
    (f_preserves_eqProp : preserves_eqProp1 f)
    : isContinuousMap f <-> preservesSupremum f.
  Proof with eauto with *.
    split; [intros f_isContinuousMap | intros f_preservesSupremum].
    - intros X X_isDirected. keep (image f X) as Y into (ensemble D2). fold Y.
      assert (Y_isDirected : isDirected Y).
      { eapply preservesDirected_if_isMonotonicMap... }
      pose proof (getSupremumOf_inCPO X X_isDirected) as [sup_X sup_X_isSupremumOf_X].
      exists (sup_X), (f sup_X). pose proof (proj2 (sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y f X sup_X (f sup_X) f_isContinuousMap X_isDirected sup_X_isSupremumOf_X) (eqProp_Reflexive (f sup_X))) as claim1...
    - ii; desnw. inversion TGT_OPEN; unnw.
      pose proof (isMonotonicMap_if_preservesSupremum f f_preserves_eqProp f_preservesSupremum) as f_isMonotonicMap.
      split; ii; desnw.
      + econstructor. eapply UPWARD_CLOSED; [inversion H_IN | eapply f_isMonotonicMap]...
      + pose proof (f_preservesSupremum X DIRECTED) as [sup [sup_Y [? [? ?]]]].
        assert (sup_X_eq_sup : sup_X == sup).
        { eapply Supremum_preserves_eqProp_wrtEnsembles... }
        assert (f_sup_X_in_Y : member (f sup_X) Y).
        { now inversion SUPREMUM_IN. }
        pose proof (liftsDirected_if_preservesSupremum f f_preserves_eqProp f_preservesSupremum X DIRECTED) as image_f_X_isDirected.
        assert (sup_Y_eq_f_sup_X : sup_Y == f sup_X).
        { rewrite sup_X_eq_sup... }
        assert (claim1 : exists y : D2, member y (image f X) /\ member y Y).
        { eapply LIMIT... }
        destruct claim1 as [y [y_in_image_f_X y_in_Y]].
        inversion y_in_image_f_X; subst y.
        exists (x). split... econstructor...
  Qed.

  Lemma supremumOfScottContinuousMaps_isWellDefined {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭)
    (F_isDirected : isDirected F)
    : forall x : D1, isDirected (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F).
  Proof with eauto with *.
    inversion F_isDirected. desnw in *. ii. destruct NONEMPTY as [f0 f0_in_F]. split; unnw.
    - exists (proj1_sig f0 x)...
    - intros y1 ? y2 ?; desnw. apply in_image_iff in H_IN1, H_IN2.
      destruct H_IN1 as [f1 [y1_eq f1_in_F]], H_IN2 as [f2 [y2_eq f2_in_F]]; subst y1 y2.
      pose proof (DIRECTED_OR_EMPTY f1 f1_in_F f2 f2_in_F) as [f3 [f3_in_F [f1_le_f3 f2_le_f3]]]; unnw.
      exists (proj1_sig f3 x)...
  Qed.

  Definition supremumOfScottContinuousMaps {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) : D1 -> D2 :=
    fun x : D1 => proj1_sig (getSupremumOf_inCPO (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) (supremumOfScottContinuousMaps_isWellDefined F F_isDirected x))
  .

  Lemma proj2_sig_supremumOfScottContinuousMaps {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) (x : D1)
    : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected x) (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F).
  Proof. exact (proj2_sig (getSupremumOf_inCPO (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) (supremumOfScottContinuousMaps_isWellDefined F F_isDirected x))). Defined.

  Lemma supremumOfScottContinuousMaps_isMonotonicMap {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭)
    (F_isDirected : isDirected F)
    : isMonotonicMap (supremumOfScottContinuousMaps F F_isDirected).
  Proof with eauto with *.
    intros x1 x2 x1_le_x2. eapply proj2_sig_supremumOfScottContinuousMaps with (x := x1). unnw.
    ii; desnw. apply in_image_iff in H_IN. destruct H_IN as [f0 [? f0_in_F]]; subst x. transitivity (proj1_sig f0 x2).
    - eapply ScottContinuousMap_isMonotonicMap... exact (proj2_sig f0).
    - eapply proj2_sig_supremumOfScottContinuousMaps with (x := x2)...
  Qed.

  Lemma supremumOfScottContinuousMaps_F_sup_X_isSupremumOf_unions_i_image_f_i_X_F {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (X : ensemble D1) (sup_X : D1)
    (F_isDirected : isDirected F)
    (X_isDirected : isDirected X)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected sup_X) (unions (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => image (fun x : D1 => proj1_sig f_i x) X) F)).
  Proof with eauto with *.
    assert (claim1 : forall f_i : ⟬ D1 ⟶ D2 ⟭, f_i \in F -> isSupremumOf (proj1_sig f_i sup_X) (image (fun x : D1 => proj1_sig f_i x) X)).
    { intros f_i f_i_in. eapply sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y... exact (proj2_sig f_i). }
    pose proof (claim2 := proj2_sig_supremumOfScottContinuousMaps F F_isDirected sup_X).
    eapply SupremumOfMapSuprema_isSupremumOf_unions.
    - intros Y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [f0 [? f0_in_F]]; subst Y...
    - intros y. split.
      + intros f_sup_X_le_y sup_Y [Y [Y_in sup_Y_isSupremumOf_Y]]. apply in_image_iff in Y_in. destruct Y_in as [f_i [? f_i_in]]; subst Y.
        pose proof (f_i_sup_X_isSupremum := claim1 f_i f_i_in).
        assert (sup_Y_eq : sup_Y == proj1_sig f_i sup_X).
        { eapply Supremum_preserves_eqProp_wrtEnsembles... }
        assert (f_i_sup_X_in : member (proj1_sig f_i sup_X) (image (fun f : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f sup_X) F)).
        { econstructor... }
        rewrite sup_Y_eq. red in sup_Y_isSupremumOf_Y, f_sup_X_le_y. rewrite <- f_sup_X_le_y. eapply claim2...
      + intros ?; desnw. eapply claim2. intros y' ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [f_i [? f_i_in]]; subst y'.
        eapply UPPER_BOUND. exists (image (fun x : D1 => proj1_sig f_i x) X). split...
  Qed.

  Theorem supremumOfScottContinuousMaps_preservesSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (X : ensemble D1) (sup_X : D1)
    (F_isDirected : isDirected F)
    (X_isDirected : isDirected X)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected sup_X) (image (supremumOfScottContinuousMaps F F_isDirected) X).
  Proof with eauto with *.
    assert (unions_image_image_comm : unions (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => image (fun x_i : D1 => proj1_sig f_i x_i) X) F) == unions (image (fun x_i : D1 => image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x_i) F) X)).
    { intros z. do 2 rewrite in_unions_iff. split; intros [Y [z_in Y_in]].
      - apply in_image_iff in Y_in. destruct Y_in as [f_i [? f_i_in]]; subst Y.
        apply in_image_iff in z_in. destruct z_in as [x_i [? x_i_in]]; subst z.
        exists (image (fun f : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f x_i) F). split...
      - apply in_image_iff in Y_in. destruct Y_in as [x_i [? x_i_in]]; subst Y.
        apply in_image_iff in z_in. destruct z_in as [f_i [? f_i_in]]; subst z.
        exists (image (fun x : D1 => proj1_sig f_i x) X). split...
    }
    assert (lemma1 : forall sup_Y : D2, isSupremumOf sup_Y (unions (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => image (fun x : D1 => proj1_sig f_i x) X) F)) <-> isSupremumOf sup_Y (unions (image (fun x : D1 => image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) X))).
    { ii. eapply Supremum_compatWith_eqProp_wrtEnsembles... }
    assert (lemma2 : forall sup_Y : D2, isSupremumOf sup_Y (unions (image (fun x : D1 => image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) X)) <-> isSupremumOf sup_Y (MapSuprema (image (fun x : D1 => image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) X))).
    { ii. symmetry. eapply SupremumOfMapSuprema_isSupremumOf_unions.
      intros Y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [x [? x_in]]; subst Y.
      exists (supremumOfScottContinuousMaps F F_isDirected x). eapply proj2_sig_supremumOfScottContinuousMaps.
    }
    pose proof (lemma3 := supremumOfScottContinuousMaps_isMonotonicMap F F_isDirected).
    assert (claim1 : forall f_i : ⟬ D1 ⟶ D2 ⟭, f_i \in F -> isSupremumOf (proj1_sig f_i sup_X) (image (fun x : D1 => proj1_sig f_i x) X)).
    { intros f_i f_i_in. eapply sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y... exact (proj2_sig f_i). }
    assert (claim2 : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected sup_X) (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i sup_X) F)).
    { eapply proj2_sig_supremumOfScottContinuousMaps. }
    assert (claim3 : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected sup_X) (unions (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => image (fun x : D1 => proj1_sig f_i x) X) F))).
    { eapply supremumOfScottContinuousMaps_F_sup_X_isSupremumOf_unions_i_image_f_i_X_F... }
    rewrite lemma1, lemma2 in claim3.
    intros y. split.
    - intros ? y' ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [x [? x_in]]; subst y'.
      eapply claim3... exists (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F). split.
      + econstructor...
      + red. eapply proj2_sig_supremumOfScottContinuousMaps.
    - ii; desnw. unnw. eapply claim3. intros upper_bound ?; desnw.
      repeat red in H_IN. destruct H_IN as [Y [Y_in upper_bound_in]].
      apply in_image_iff in Y_in. destruct Y_in as [x [? x_in]]; subst Y.
      red in upper_bound_in. transitivity (supremumOfScottContinuousMaps F F_isDirected x).
      + eapply eqProp_implies_leProp, Supremum_preserves_eqProp_wrtEnsembles.
        { exact (upper_bound_in). }
        { eapply proj2_sig_supremumOfScottContinuousMaps. }
        { reflexivity. }
      + eapply UPPER_BOUND...
  Qed.

  Corollary supremumOfScottContinuousMaps_isContinuousMap {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭)
    (F_isDirected : isDirected F)
    : isContinuousMap (supremumOfScottContinuousMaps F F_isDirected).
  Proof with eauto with *.
    eapply the_main_reason_for_introducing_ScottTopology.
    - ii. eapply leProp_Antisymmetric; eapply supremumOfScottContinuousMaps_isMonotonicMap...
    - intros X X_isDirected; unnw.
      pose proof (getSupremumOf_inCPO X X_isDirected) as [sup_X sup_X_isSupremumOf_X].
      exists (sup_X), (supremumOfScottContinuousMaps F F_isDirected sup_X).
      pose proof (supremumOfScottContinuousMaps_preservesSupremum F X sup_X F_isDirected X_isDirected sup_X_isSupremumOf_X) as claim1...
  Qed.

  Definition SupremumOfScottContinuousMaps {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) : ⟬ D1 ⟶ D2 ⟭ :=
    @exist (D1 -> D2) isContinuousMap (supremumOfScottContinuousMaps F F_isDirected) (supremumOfScottContinuousMaps_isContinuousMap F F_isDirected)
  .

  Lemma SupremumOfScottContinuousMaps_isSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F)
    : isSupremumOf (SupremumOfScottContinuousMaps F F_isDirected) F.
  Proof with eauto with *.
    intros f. split.
    - intros ? f_i ?; desnw. rewrite <- SUPREMUM_LE_UPPER_BOUND. intros x. simpl.
      eapply proj2_sig_supremumOfScottContinuousMaps with (F := F) (F_isDirected := F_isDirected)...
    - intros ?; desnw. intros x; simpl. unfold supremumOfScottContinuousMaps.
      destruct (getSupremumOf_inCPO (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) (supremumOfScottContinuousMaps_isWellDefined F F_isDirected x)) as [sup_F_x sup_F_x_isSupremum]; simpl.
      eapply sup_F_x_isSupremum. intros y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [f_i [? f_i_in]]; subst y. eapply UPPER_BOUND...
  Qed.

  Definition bottomOfScottContinuousMaps {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} : D1 -> D2 :=
    fun x : D1 => proj1_sig getBottom_inCPO
  .

  Lemma bottomOfScottContinuousMaps_isContinuousMap {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2}
    : isContinuousMap (bottomOfScottContinuousMaps (D1 := D1) (D2 := D2)).
  Proof with eauto with *.
    intros O O_isOpen. unfold bottomOfScottContinuousMaps. unnw. inversion O_isOpen. unnw. split.
    - ii; desnw. apply in_preimage_iff in H_IN. des. econstructor...
    - ii; desnw. destruct DIRECTED as [[x0 x0_in_X] ?]; desnw. apply in_preimage_iff in SUPREMUM_IN. des.
      exists (x0). split... econstructor...
  Qed.

  Definition BottomOfScottContinuousMaps {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} : ⟬ D1 ⟶ D2 ⟭ :=
    @exist (D1 -> D2) isContinuousMap bottomOfScottContinuousMaps bottomOfScottContinuousMaps_isContinuousMap
  .

  Lemma BottomOfScottContinuousMaps_isBottom {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2}
    : forall f : ⟬ D1 ⟶ D2 ⟭, BottomOfScottContinuousMaps =< f.
  Proof. intros f. exact (fun x : D1 => proj2_sig getBottom_inCPO (proj1_sig f x)). Qed.

  Global Instance ScottContinuousMaps_asCPO {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} (D1_isCPO : isCPO D1) (D2_isCPO : isCPO D2) : isCPO ⟬ D1 ⟶ D2 ⟭ :=
    { getBottom_inCPO := @exist _ _ BottomOfScottContinuousMaps BottomOfScottContinuousMaps_isBottom
    ; getSupremumOf_inCPO (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) := @exist _ _ (SupremumOfScottContinuousMaps F F_isDirected) (SupremumOfScottContinuousMaps_isSupremum F F_isDirected)
    }
  .

  Global Existing Instance pair_isPoset.

  Lemma bottom_of_pair_isBottom {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2}
    : forall x : D1 * D2, (proj1_sig getBottom_inCPO, proj1_sig getBottom_inCPO) =< x.
  Proof. intros [x1 x2]. split; [exact (proj2_sig getBottom_inCPO x1) | exact (proj2_sig getBottom_inCPO x2)]. Qed.

  Lemma image_fst_liftsDirected {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} (X : ensemble (D1 * D2))
    (X_isDirected : isDirected X)
    : isDirected (image fst X).
  Proof with eauto with *.
    inversion X_isDirected; desnw. destruct x0 as [x1_0 x2_0]. split; unnw.
    - exists (x1_0)...
    - intros x1_1 ? x2_1 ?; desnw. apply in_image_iff in H_IN1, H_IN2.
      destruct H_IN1 as [[x1 x1_2] [? H_IN1]]; simpl in *; subst x1.
      destruct H_IN2 as [[x1 x2_2] [? H_IN2]]; simpl in *; subst x1.
      pose proof (DIRECTED_OR_EMPTY _ H_IN1 _ H_IN2) as [[x3_1 x3_2] [? [[? ?] [? ?]]]]; desnw; simpl in *.
      exists (x3_1). split...
  Qed.

  Lemma image_snd_liftsDirected {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} (X : ensemble (D1 * D2))
    (X_isDirected : isDirected X)
    : isDirected (image snd X).
  Proof with eauto with *.
    inversion X_isDirected; desnw. destruct x0 as [x1_0 x2_0]. split; unnw.
    - exists (x2_0)...
    - intros x1_2 ? x2_2 ?; desnw. apply in_image_iff in H_IN1, H_IN2.
      destruct H_IN1 as [[x1_1 x2] [? H_IN1]]; simpl in *; subst x2.
      destruct H_IN2 as [[x2_1 x2] [? H_IN2]]; simpl in *; subst x2.
      pose proof (DIRECTED_OR_EMPTY _ H_IN1 _ H_IN2) as [[x3_1 x3_2] [? [[? ?] [? ?]]]]; desnw; simpl in *.
      exists (x3_2). split...
  Qed.

  Lemma supremum_of_pair_isSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (X : ensemble (D1 * D2))
    (X_isDirected : isDirected X)
    : isSupremumOf (proj1_sig (getSupremumOf_inCPO (image fst X) (image_fst_liftsDirected X X_isDirected)), proj1_sig (getSupremumOf_inCPO (image snd X) (image_snd_liftsDirected X X_isDirected))) X.
  Proof with eauto with *.
    intros [z1 z2]. split; intros ?; desnw; unnw.
    - destruct SUPREMUM_LE_UPPER_BOUND as [SUPREMUM_LE_UPPER_BOUND1 SUPREMUM_LE_UPPER_BOUND2]; simpl in *.
      intros [x1 x2] ?; desnw. split; simpl.
      + eapply SUPREMUM_LE_UPPER_BOUND1.
  Qed.

  Definition seperately_monotonic {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} (f : D1 * D2 -> D3) : Prop :=
    ⟪ MON_FST_ARG : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2)) ⟫ /\ ⟪ MON_SND_ARG : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2)) ⟫
  .

  Lemma seperately_monotonic_iff_monotonic {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} (f : D1 * D2 -> D3)
    : seperately_monotonic f <-> isMonotonicMap f.
  Proof with eauto with *.
    split; [intros [? ?]; desnw | intros f_monotonic].
    - ii. destruct x as [x1 x2]. destruct x' as [x1' x2']. inversion x_le_x'; simpl in *.
      transitivity (f (x1, x2')); [eapply MON_FST_ARG | eapply MON_SND_ARG]...
    - split; ii; eapply f_monotonic; split...
  Qed.

(*
  Lemma f_x1_sup_X2_eq_sup_f_x1_X2 {dom1 : Type} {dom2 : Type} {cod : Type} {dom1_isPoset : isPoset dom1} {dom2_isPoset : isPoset dom2} {cod_isPoset : isPoset cod} (f : dom1 * dom2 -> cod) (x1 : dom1) (X2 : ensemble dom2) (sup_X2 : dom2)
    (f_isContinuousMap : isContinuousMap f)
    (X2_isDirected : isDirected X2)
    (sup_X2_isSupremumOf_X2 : isSupremumOf sup_X2 X2)
    : isSupremumOf (f (x1, sup_X2)) (image (fun x2 : dom2 => f (x1, x2)) X2).
  Proof with eauto with *.
    revert x1 X2 X2_isDirected sup_X2 sup_X2_isSupremumOf_X2.
    assert (f_isMonotonicMap : isMonotonicMap f).
    { eapply ScottContinuousMap_isMonotonicMap... }
    assert (f_isMonotonicMap_at2 : forall x1 : dom1, isMonotonicMap (fun x2 : dom2 => f (x1, x2))).
    { eapply seperately_monotonic_iff_monotonic... }
    assert (f_preserves_eqProp : preserves_eqProp1 f).
    { intros [x1 x2] [x1' x2'] [H_eq1 H_eq2]; simpl in *. eapply leProp_Antisymmetric; eapply f_isMonotonicMap; split... }
    intros x1.
    assert (f_preserves_eqProp_at2 : preserves_eqProp1 (fun x2 : dom2 => f (x1, x2))).
    { ii. eapply leProp_Antisymmetric; eapply f_isMonotonicMap_at2... }
    intros X2 X2_isDirected.
    set (X := (image (fun x2 : dom2 => (x1, x2)) X2)).
    set (Y := (image (fun x2 : dom2 => f (x1, x2)) X2)).
    assert (claim1 : isDirected X).
    { inversion X2_isDirected; desnw. rename x0 into x2_0. split; unnw.
      - exists (x1, x2_0)...
      - intros [x1_1 x2_1] x1_in_X [x1_2 x2_2] x2_in_X; unnw. apply in_image_iff in x1_in_X, x2_in_X.
        destruct x1_in_X as [x2 [H_eq x2_1_in]]. inversion H_eq; subst x1_1 x2. clear H_eq.
        destruct x2_in_X as [x2 [H_eq x2_2_in]]. inversion H_eq; subst x1_2 x2. clear H_eq.
        pose proof (DIRECTED_OR_EMPTY x2_1 x2_1_in x2_2 x2_2_in) as [x2_3 [? [x2_1_le_x2_3 x2_2_le_x2_3]]]; desnw.
        exists (x1, x2_3). repeat split...
    }
    intros sup_X2 sup_X2_isSupremumOf_X2.
    pose proof (getSupremumOf_inCPO X claim1) as [sup_X sup_X_isSupremumOf_X].
  Qed. *)

*)

End BasicCpoTheory.
