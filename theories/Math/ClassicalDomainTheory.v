Require Import Coq.Lists.List.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeClassic.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BasicGeneralTopology.
Require Import DschingisKhan.Logic.ScottTopology.

Module BasicCpoTheory.

  Import ListNotations MathProps MathClasses BasicPosetTheory BasicGeneralTopology DomainTheoryHelper ScottTopology ExclusiveMiddle.

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
    : f sup_X == getSupremumOf_inCPO (image f X) image_f_X_isDirected.
  Proof with eauto with *.
    assert (f_isMonotonicMap : isMonotonicMap f) by now eapply ScottContinuousMap_isMonotonicMap.
    revert image_f_X_isDirected. keep (image f X) as Y into (ensemble D2). fold Y. ii.
    set (sup_Y := getSupremumOf_inCPO Y image_f_X_isDirected).
    pose proof (sup_Y_isSupremumOf_Y := getSupremumOf_inCPO_isSupremum Y image_f_X_isDirected).
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
      eapply Supremum_unique.
      + exact (getSupremumOf_inCPO_isSupremum (image f X) image_f_X_isDirected).
      + exact (sup_Y_isSupremumOf_image_f_X).
      + reflexivity.
    - intros f_sup_X_eq_sup_Y. rewrite <- f_sup_X_eq_sup_Y.
      rewrite f_sup_X_eq_sup_image_f_X with (f := f) (f_isContinuousMap := f_isContinuousMap) (X_isDirected := X_isDirected) (sup_X_isSupremumOf_X := sup_X_isSupremumOf_X) (image_f_X_isDirected := image_f_X_isDirected).
      exact (getSupremumOf_inCPO_isSupremum (image f X) image_f_X_isDirected).
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
    { eapply f_preserves_eqProp. eapply Supremum_unique; eauto with *. }
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
      set (sup_X := getSupremumOf_inCPO X X_isDirected).
      pose proof (sup_X_isSupremumOf_X := getSupremumOf_inCPO_isSupremum X X_isDirected).
      exists (sup_X), (f sup_X). pose proof (proj2 (sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y f X sup_X (f sup_X) f_isContinuousMap X_isDirected sup_X_isSupremumOf_X) (eqProp_Reflexive (f sup_X))) as claim1...
    - ii; desnw. inversion TGT_OPEN; unnw.
      pose proof (isMonotonicMap_if_preservesSupremum f f_preserves_eqProp f_preservesSupremum) as f_isMonotonicMap.
      split; ii; desnw.
      + econstructor. eapply UPWARD_CLOSED; [inversion H_IN | eapply f_isMonotonicMap]...
      + pose proof (f_preservesSupremum X DIRECTED) as [sup [sup_Y [? [? ?]]]].
        assert (sup_X_eq_sup : sup_X == sup).
        { eapply Supremum_unique... }
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
    inversion F_isDirected. desnw'. ii. destruct NONEMPTY as [f0 f0_in_F]. split; unnw.
    - exists (proj1_sig f0 x)...
    - intros y1 ? y2 ?; desnw. apply in_image_iff in H_IN1, H_IN2.
      destruct H_IN1 as [f1 [y1_eq f1_in_F]], H_IN2 as [f2 [y2_eq f2_in_F]]; subst y1 y2.
      pose proof (DIRECTED_OR_EMPTY f1 f1_in_F f2 f2_in_F) as [f3 [f3_in_F [f1_le_f3 f2_le_f3]]]; unnw.
      exists (proj1_sig f3 x)...
  Qed.

  Definition supremumOfScottContinuousMaps {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) : D1 -> D2 :=
    fun x : D1 => getSupremumOf_inCPO (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) (supremumOfScottContinuousMaps_isWellDefined F F_isDirected x)
  .

  Lemma supremumOfScottContinuousMaps_isSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) (x : D1)
    : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected x) (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F).
  Proof. exact (getSupremumOf_inCPO_isSupremum (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) (supremumOfScottContinuousMaps_isWellDefined F F_isDirected x)). Defined.

  Lemma supremumOfScottContinuousMaps_isMonotonicMap {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭)
    (F_isDirected : isDirected F)
    : isMonotonicMap (supremumOfScottContinuousMaps F F_isDirected).
  Proof with eauto with *.
    intros x1 x2 x1_le_x2. eapply supremumOfScottContinuousMaps_isSupremum with (x := x1). unnw.
    ii; desnw. apply in_image_iff in H_IN. destruct H_IN as [f0 [? f0_in_F]]; subst x. transitivity (proj1_sig f0 x2).
    - eapply ScottContinuousMap_isMonotonicMap... exact (proj2_sig f0).
    - eapply supremumOfScottContinuousMaps_isSupremum with (x := x2)...
  Qed.

  Lemma supremumOfScottContinuousMaps_F_sup_X_isSupremumOf_unions_i_image_f_i_X_F {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (X : ensemble D1) (sup_X : D1)
    (F_isDirected : isDirected F)
    (X_isDirected : isDirected X)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected sup_X) (unions (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => image (fun x : D1 => proj1_sig f_i x) X) F)).
  Proof with eauto with *.
    assert (claim1 : forall f_i : ⟬ D1 ⟶ D2 ⟭, f_i \in F -> isSupremumOf (proj1_sig f_i sup_X) (image (fun x : D1 => proj1_sig f_i x) X)).
    { intros f_i f_i_in. eapply sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y... exact (proj2_sig f_i). }
    pose proof (claim2 := supremumOfScottContinuousMaps_isSupremum F F_isDirected sup_X).
    eapply SupremumOfMapSuprema_isSupremumOf_unions.
    - intros Y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [f0 [? f0_in_F]]; subst Y...
    - intros y. split.
      + intros f_sup_X_le_y sup_Y [Y [Y_in sup_Y_isSupremumOf_Y]]. apply in_image_iff in Y_in. destruct Y_in as [f_i [? f_i_in]]; subst Y.
        pose proof (f_i_sup_X_isSupremum := claim1 f_i f_i_in).
        assert (sup_Y_eq : sup_Y == proj1_sig f_i sup_X).
        { eapply Supremum_unique... }
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
      exists (supremumOfScottContinuousMaps F F_isDirected x). eapply supremumOfScottContinuousMaps_isSupremum.
    }
    pose proof (lemma3 := supremumOfScottContinuousMaps_isMonotonicMap F F_isDirected).
    assert (claim1 : forall f_i : ⟬ D1 ⟶ D2 ⟭, f_i \in F -> isSupremumOf (proj1_sig f_i sup_X) (image (fun x : D1 => proj1_sig f_i x) X)).
    { intros f_i f_i_in. eapply sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y... exact (proj2_sig f_i). }
    assert (claim2 : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected sup_X) (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i sup_X) F)).
    { eapply supremumOfScottContinuousMaps_isSupremum. }
    assert (claim3 : isSupremumOf (supremumOfScottContinuousMaps F F_isDirected sup_X) (unions (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => image (fun x : D1 => proj1_sig f_i x) X) F))).
    { eapply supremumOfScottContinuousMaps_F_sup_X_isSupremumOf_unions_i_image_f_i_X_F... }
    rewrite lemma1, lemma2 in claim3.
    intros y. split.
    - intros ? y' ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [x [? x_in]]; subst y'.
      eapply claim3... exists (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F). split.
      + econstructor...
      + red. eapply supremumOfScottContinuousMaps_isSupremum.
    - ii; desnw. unnw. eapply claim3. intros upper_bound ?; desnw.
      repeat red in H_IN. destruct H_IN as [Y [Y_in upper_bound_in]].
      apply in_image_iff in Y_in. destruct Y_in as [x [? x_in]]; subst Y.
      red in upper_bound_in. transitivity (supremumOfScottContinuousMaps F F_isDirected x).
      + eapply eqProp_implies_leProp, Supremum_unique.
        { exact (upper_bound_in). }
        { eapply supremumOfScottContinuousMaps_isSupremum. }
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
      pose proof (getSupremumOf_inCPO_isSupremum X X_isDirected) as sup_X_isSupremumOf_X.
      exists (getSupremumOf_inCPO X X_isDirected), (supremumOfScottContinuousMaps F F_isDirected (getSupremumOf_inCPO X X_isDirected)).
      pose proof (supremumOfScottContinuousMaps_preservesSupremum F X (getSupremumOf_inCPO X X_isDirected) F_isDirected X_isDirected sup_X_isSupremumOf_X) as claim1...
  Qed.

  Definition SupremumOfScottContinuousMaps {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) : ⟬ D1 ⟶ D2 ⟭ :=
    @exist (D1 -> D2) isContinuousMap (supremumOfScottContinuousMaps F F_isDirected) (supremumOfScottContinuousMaps_isContinuousMap F F_isDirected)
  .

  Lemma SupremumOfScottContinuousMaps_isSupremum {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F)
    : isSupremumOf (SupremumOfScottContinuousMaps F F_isDirected) F.
  Proof with eauto with *.
    intros f. split.
    - intros ? f_i ?; desnw. rewrite <- SUPREMUM_LE_UPPER_BOUND. intros x. simpl.
      eapply supremumOfScottContinuousMaps_isSupremum with (F := F) (F_isDirected := F_isDirected)...
    - intros ?; desnw. intros x; simpl. unfold supremumOfScottContinuousMaps.
      set (sup_F_x := getSupremumOf_inCPO (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) (supremumOfScottContinuousMaps_isWellDefined F F_isDirected x)).
      pose proof (sup_F_x_isSupremum := getSupremumOf_inCPO_isSupremum (image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => proj1_sig f_i x) F) (supremumOfScottContinuousMaps_isWellDefined F F_isDirected x)).
      eapply sup_F_x_isSupremum. intros y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [f_i [? f_i_in]]; subst y. eapply UPPER_BOUND...
  Qed.

  Definition bottomOfScottContinuousMaps {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} : D1 -> D2 :=
    fun x : D1 => getBottom_inCPO
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
  Proof. intros f. exact (fun x : D1 => getBottom_inCPO_isBottom (proj1_sig f x)). Qed.

  Global Instance ScottContinuousMaps_asCPO {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} (D1_isCPO : isCPO D1) (D2_isCPO : isCPO D2) : isCPO ⟬ D1 ⟶ D2 ⟭ :=
    { getBottom_inCPO := BottomOfScottContinuousMaps
    ; getSupremumOf_inCPO (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) := SupremumOfScottContinuousMaps F F_isDirected
    ; getBottom_inCPO_isBottom := BottomOfScottContinuousMaps_isBottom
    ; getSupremumOf_inCPO_isSupremum (F : ensemble ⟬ D1 ⟶ D2 ⟭) (F_isDirected : isDirected F) := (SupremumOfScottContinuousMaps_isSupremum F F_isDirected)
    }
  .

  Global Existing Instance pair_isPoset.

  Lemma bottom_of_pair_isBottom {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2}
    : forall x : D1 * D2, (getBottom_inCPO, getBottom_inCPO) =< x.
  Proof. intros [x1 x2]. split; [exact (getBottom_inCPO_isBottom x1) | exact (getBottom_inCPO_isBottom x2)]. Qed.

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
    : isSupremumOf (getSupremumOf_inCPO (image fst X) (image_fst_liftsDirected X X_isDirected), getSupremumOf_inCPO (image snd X) (image_snd_liftsDirected X X_isDirected)) X.
  Proof with eauto with *.
    intros [z1 z2]. split; intros ?; desnw; unnw.
    - destruct SUPREMUM_LE_UPPER_BOUND as [SUPREMUM_LE_UPPER_BOUND1 SUPREMUM_LE_UPPER_BOUND2]; simpl in *.
      intros [x1 x2] ?; desnw. split; simpl.
      + rewrite <- SUPREMUM_LE_UPPER_BOUND1. eapply getSupremumOf_inCPO_isSupremum...
      + rewrite <- SUPREMUM_LE_UPPER_BOUND2. eapply getSupremumOf_inCPO_isSupremum...
    - inversion X_isDirected; desnw. destruct x0 as [x1_0 x2_0]. split; simpl.
      + eapply getSupremumOf_inCPO_isSupremum.
        intros x1 ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [[x1_1 x2_1] [? H_IN]]; subst x1.
        simpl. exploit (UPPER_BOUND (x1_1, x2_1)) as [? ?]...
      + eapply getSupremumOf_inCPO_isSupremum.
        intros x2 ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [[x1_1 x2_1] [? H_IN]]; subst x2.
        simpl. exploit (UPPER_BOUND (x1_1, x2_1)) as [? ?]...
  Qed.

  Global Instance pair_isCPO {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} (D1_isCPO : isCPO D1) (D2_isCPO : isCPO D2) : isCPO (D1 * D2) :=
    { getBottom_inCPO := (getBottom_inCPO, getBottom_inCPO)
    ; getSupremumOf_inCPO (X : ensemble (D1 * D2)) (X_isDirected : isDirected X) := (getSupremumOf_inCPO (image fst X) (image_fst_liftsDirected X X_isDirected), getSupremumOf_inCPO (image snd X) (image_snd_liftsDirected X X_isDirected))
    ; getBottom_inCPO_isBottom := bottom_of_pair_isBottom
    ; getSupremumOf_inCPO_isSupremum := supremum_of_pair_isSupremum
    }
  .

  Definition seperately_monotonic {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} (f : D1 * D2 -> D3) : Prop :=
    ⟪ MON_FST_ARG : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2)) ⟫ /\ ⟪ MON_SND_ARG : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2)) ⟫
  .

  Lemma seperately_monotonic_iff_monotonic {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} (f : D1 * D2 -> D3)
    : seperately_monotonic f <-> isMonotonicMap f.
  Proof with eauto with *.
    split; [intros [? ?]; desnw | intros f_monotonic].
    - ii. destruct x as [x1 x2]. destruct x' as [x1' x2']. inversion x_le_x'; simpl in *.
      transitivity (f (x1', x2)); [eapply MON_FST_ARG | eapply MON_SND_ARG]...
    - split; ii; eapply f_monotonic; split...
  Qed.

  Lemma f_x1_sup_X2_eq_sup_f_x1_X2 {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} {D3_isCPO : isCPO D3} (f : D1 * D2 -> D3) (x1 : D1) (X2 : ensemble D2) (sup_X2 : D2)
    (f_isContinuousMap : isContinuousMap f)
    (X2_isDirected : isDirected X2)
    (sup_X2_isSupremumOf_X2 : isSupremumOf sup_X2 X2)
    : isSupremumOf (f (x1, sup_X2)) (image (fun x2 : D2 => f (x1, x2)) X2).
  Proof with eauto with *.
    revert x1 X2 X2_isDirected sup_X2 sup_X2_isSupremumOf_X2.
    assert (f_isMonotonicMap : isMonotonicMap f).
    { eapply ScottContinuousMap_isMonotonicMap... }
    assert (f_isMonotonicMap_at2 : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2))).
    { eapply seperately_monotonic_iff_monotonic... }
    assert (f_preserves_eqProp : preserves_eqProp1 f).
    { intros [x1 x2] [x1' x2'] [H_eq1 H_eq2]; simpl in *. eapply leProp_Antisymmetric; eapply f_isMonotonicMap; split... }
    intros x1.
    assert (f_preserves_eqProp_at2 : preserves_eqProp1 (fun x2 : D2 => f (x1, x2))).
    { ii. eapply leProp_Antisymmetric; eapply f_isMonotonicMap_at2... }
    intros X2 X2_isDirected.
    set (X := image (fun x2 : D2 => (x1, x2)) X2).
    set (Y := image (fun x2 : D2 => f (x1, x2)) X2).
    assert (X_isDirected : isDirected X).
    { inversion X2_isDirected; desnw. rename x0 into x2_0. split; unnw.
      - exists (x1, x2_0)...
      - intros [x1_1 x2_1] x1_in_X [x1_2 x2_2] x2_in_X; unnw. apply in_image_iff in x1_in_X, x2_in_X.
        destruct x1_in_X as [x2 [H_eq x2_1_in]]. inversion H_eq; subst x1_1 x2. clear H_eq.
        destruct x2_in_X as [x2 [H_eq x2_2_in]]. inversion H_eq; subst x1_2 x2. clear H_eq.
        pose proof (DIRECTED_OR_EMPTY x2_1 x2_1_in x2_2 x2_2_in) as [x2_3 [? [x2_1_le_x2_3 x2_2_le_x2_3]]]; desnw.
        exists (x1, x2_3). repeat split...
    }
    intros sup_X2 sup_X2_isSupremumOf_X2.
    set (sup_X := getSupremumOf_inCPO X X_isDirected). pose proof (getSupremumOf_inCPO_isSupremum X X_isDirected) as sup_X_isSupremumOf_X. fold sup_X in sup_X_isSupremumOf_X.
    assert (claim1 : (x1, sup_X2) == sup_X).
    { eapply Supremum_unique with (X2 := X); [intros [x_1 x_2] | trivial | reflexivity]. split.
      - intros [x1_le_x_1 sup_X2_le_x2] [x_1' x_2'] H_IN'.
        apply in_image_iff in H_IN'. destruct H_IN' as [x2 [H_EQ x2_in]].
        apply pair_equal_spec in H_EQ. destruct H_EQ; subst x_1' x_2'. split; simpl in *.
        + trivial.
        + eapply sup_X2_isSupremumOf_X2...
      - intros ?; desnw. split; simpl.
        + inversion X2_isDirected; desnw. enough (to_show : (x1, x0) =< (x_1, x_2)) by exact (proj1 to_show). eapply UPPER_BOUND...
        + eapply sup_X2_isSupremumOf_X2. intros x2 ?; desnw. eapply UPPER_BOUND with (x := (x1, x2))...
    }
    assert (claim2 : f (x1, sup_X2) == f sup_X).
    { eapply f_preserves_eqProp... }
    assert (PRESERVES_SUPREMUM : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremumOf sup_X' X /\ isSupremumOf sup_Y' (image f X) /\ f sup_X' == sup_Y').
    { eapply the_main_reason_for_introducing_ScottTopology with (f := f)... }
    destruct PRESERVES_SUPREMUM as [sup_X' [sup_Y' [sup_X'_isSupremum [sup_Y'_isSupremum f_x1_sup_X'_eq_sup_Y']]]].
    assert (claim3 : isSupremumOf (f sup_X) (image f X)).
    { eapply Supremum_congruence with (sup_X := f sup_X') (X := image f X).
      - eapply f_preserves_eqProp. symmetry. eapply Supremum_unique...
      - reflexivity.
      - rewrite f_x1_sup_X'_eq_sup_Y'...
    }
    eapply Supremum_congruence with (sup_X := f sup_X) (X := image f X); trivial.
    - symmetry...
    - intros y. split; intros H_IN.
      + apply in_image_iff in H_IN. destruct H_IN as [[x_1 x_2] [? H_IN]]; subst y. apply in_image_iff in H_IN. destruct H_IN as [x2 [H_EQ H_IN]]. apply pair_equal_spec in H_EQ. des...
      + apply in_image_iff in H_IN. destruct H_IN as [x2 [? H_IN]]; subst y...
  Qed.

  Corollary f2_cont_if_f_cont {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} {D3_isCPO : isCPO D3} (f : D1 * D2 -> D3) (x1 : D1)
    (f_isContinuousMap : isContinuousMap f)
    : isContinuousMap (fun x2 : D2 => f (x1, x2)).
  Proof with eauto with *.
    revert x1.
    assert (f_monotonic : isMonotonicMap f).
    { eapply ScottContinuousMap_isMonotonicMap... }
    assert (f2_isMonotonicMap : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2))).
    { ii. eapply ScottContinuousMap_isMonotonicMap; trivial. split... }
    assert (f_preserves_eqProp : preserves_eqProp1 f).
    { intros [x1 x2] [x1' x2'] [? ?]; simpl in *. eapply monotonic_guarantees_eqProp_lifted1; trivial. split... }
    intros x1. eapply the_main_reason_for_introducing_ScottTopology.
    - ii. eapply f_preserves_eqProp. split...
    - intros X2 X2_isDirected; unnw. set (sup_X2 := getSupremumOf_inCPO X2 X2_isDirected). exists (sup_X2), (f (x1, sup_X2)).
      pose proof (getSupremumOf_inCPO_isSupremum X2 X2_isDirected) as claim1. split; trivial. split.
      + eapply f_x1_sup_X2_eq_sup_f_x1_X2...
      + reflexivity.
  Qed.

  Lemma f_sup_X1_x2_eq_sup_f_X1_x2 {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} {D3_isCPO : isCPO D3} (f : D1 * D2 -> D3) (x2 : D2) (X1 : ensemble D1) (sup_X1 : D1)
    (f_isContinuousMap : isContinuousMap f)
    (X1_isDirected : isDirected X1)
    (sup_X1_isSupremumOf_X1 : isSupremumOf sup_X1 X1)
    : isSupremumOf (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1).
  Proof with eauto with *.
    revert x2 X1 X1_isDirected sup_X1 sup_X1_isSupremumOf_X1.
    assert (f_isMonotonicMap : isMonotonicMap f).
    { eapply ScottContinuousMap_isMonotonicMap... }
    assert (f_isMonotonicMap_at2 : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2))).
    { eapply seperately_monotonic_iff_monotonic... }
    assert (f_preserves_eqProp : preserves_eqProp1 f).
    { intros [x1 x2] [x1' x2'] [H_eq1 H_eq2]; simpl in *. eapply leProp_Antisymmetric; eapply f_isMonotonicMap; split... }
    intros x2.
    assert (f_preserves_eqProp_at2 : preserves_eqProp1 (fun x1 : D1 => f (x1, x2))).
    { ii. eapply leProp_Antisymmetric; eapply f_isMonotonicMap_at2... }
    intros X1 X1_isDirected.
    set (X := image (fun x1 : D1 => (x1, x2)) X1).
    set (Y := image (fun x1 : D1 => f (x1, x2)) X1).
    assert (X_isDirected : isDirected X).
    { inversion X1_isDirected; desnw. rename x0 into x1_0. split; unnw.
      - exists (x1_0, x2)...
      - intros [x1_1 x2_1] x1_in_X [x1_2 x2_2] x2_in_X; unnw. apply in_image_iff in x1_in_X, x2_in_X.
        destruct x1_in_X as [x1 [H_eq x1_1_in]]. inversion H_eq; subst x2_1 x1. clear H_eq.
        destruct x2_in_X as [x1 [H_eq x1_2_in]]. inversion H_eq; subst x2_2 x1. clear H_eq.
        pose proof (DIRECTED_OR_EMPTY x1_1 x1_1_in x1_2 x1_2_in) as [x1_3 [? [x1_1_le_x1_3 x1_2_le_x1_3]]]; desnw.
        exists (x1_3, x2). repeat split...
    }
    intros sup_X1 sup_X1_isSupremumOf_X1.
    set (sup_X := getSupremumOf_inCPO X X_isDirected). pose proof (getSupremumOf_inCPO_isSupremum X X_isDirected) as sup_X_isSupremumOf_X. fold sup_X in sup_X_isSupremumOf_X.
    assert (claim1 : (sup_X1, x2) == sup_X).
    { eapply Supremum_unique with (X2 := X); [intros [x_1 x_2] | trivial | reflexivity]. split.
      - intros [sup_X1_le_x1 x2_le_x_2] [x_1' x_2'] H_IN'.
        apply in_image_iff in H_IN'. destruct H_IN' as [x1 [H_EQ x1_in]].
        apply pair_equal_spec in H_EQ. destruct H_EQ; subst x_1' x_2'. split; simpl in *.
        + eapply sup_X1_isSupremumOf_X1...
        + trivial.
      - intros ?; desnw. split; simpl.
        + eapply sup_X1_isSupremumOf_X1. intros x1 ?; desnw. eapply UPPER_BOUND with (x := (x1, x2))...
        + inversion X1_isDirected; desnw. enough (to_show : (x0, x2) =< (x_1, x_2)) by exact (proj2 to_show). eapply UPPER_BOUND...
    }
    assert (claim2 : f (sup_X1, x2) == f sup_X).
    { eapply f_preserves_eqProp... }
    assert (PRESERVES_SUPREMUM : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremumOf sup_X' X /\ isSupremumOf sup_Y' (image f X) /\ f sup_X' == sup_Y').
    { eapply the_main_reason_for_introducing_ScottTopology with (f := f)... }
    destruct PRESERVES_SUPREMUM as [sup_X' [sup_Y' [sup_X'_isSupremum [sup_Y'_isSupremum f_x1_sup_X'_eq_sup_Y']]]].
    assert (claim3 : isSupremumOf (f sup_X) (image f X)).
    { eapply Supremum_congruence with (sup_X := f sup_X') (X := image f X).
      - eapply f_preserves_eqProp. symmetry. eapply Supremum_unique...
      - reflexivity.
      - rewrite f_x1_sup_X'_eq_sup_Y'...
    }
    eapply Supremum_congruence with (sup_X := f sup_X) (X := image f X); trivial.
    - symmetry...
    - intros y. split; intros H_IN.
      + apply in_image_iff in H_IN. destruct H_IN as [[x_1 x_2] [? H_IN]]; subst y. apply in_image_iff in H_IN. destruct H_IN as [x1 [H_EQ H_IN]]. apply pair_equal_spec in H_EQ. des...
      + apply in_image_iff in H_IN. destruct H_IN as [x1 [? H_IN]]; subst y...
  Qed.

  Corollary f1_cont_if_f_cont {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} {D3_isCPO : isCPO D3} (f : D1 * D2 -> D3) (x2 : D2)
    (f_isContinuousMap : isContinuousMap f)
    : isContinuousMap (fun x1 : D1 => f (x1, x2)).
  Proof with eauto with *.
    revert x2.
    assert (f_monotonic : isMonotonicMap f).
    { eapply ScottContinuousMap_isMonotonicMap... }
    assert (f1_isMonotonicMap : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2))).
    { ii. eapply ScottContinuousMap_isMonotonicMap; trivial. split... }
    assert (f_preserves_eqProp : preserves_eqProp1 f).
    { intros [x1 x2] [x1' x2'] [? ?]; simpl in *. eapply monotonic_guarantees_eqProp_lifted1; trivial. split... }
    intros x2. eapply the_main_reason_for_introducing_ScottTopology.
    - ii. eapply f_preserves_eqProp. split...
    - intros X1 X1_isDirected; unnw. set (sup_X1 := getSupremumOf_inCPO X1 X1_isDirected). exists (sup_X1), (f (sup_X1, x2)).
      pose proof (getSupremumOf_inCPO_isSupremum X1 X1_isDirected) as claim1. split; trivial. split.
      + eapply f_sup_X1_x2_eq_sup_f_X1_x2...
      + reflexivity.
  Qed.

  Lemma f_sup_X1_sup_X2_eq_sup_f_X1_X2 {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} {D3_isCPO : isCPO D3} (f : D1 * D2 -> D3) (X : ensemble (D1 * D2)) (sup_X1 : D1) (sup_X2 : D2)
    (f1_isContinuousMap : forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2)))
    (f2_isContinuousMap : forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2)))
    (X_isDirected : isDirected X)
    (sup_X1_isSupremumOf_X1 : isSupremumOf sup_X1 (image fst X))
    (sup_X2_isSupremumOf_X2 : isSupremumOf sup_X2 (image snd X))
    : isSupremumOf (f (sup_X1, sup_X2)) (image f X).
  Proof with eauto with *.
    revert X X_isDirected sup_X1 sup_X2 sup_X1_isSupremumOf_X1 sup_X2_isSupremumOf_X2.
    assert (f1_isMonotonicMap : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2))).
    { intros x2. eapply ScottContinuousMap_isMonotonicMap... }
    assert (f2_isMonotonicMap : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2))).
    { intros x1. eapply ScottContinuousMap_isMonotonicMap... }
    assert (f1_preserves_eqProp : forall x2 : D2, preserves_eqProp1 (fun x1 : D1 => f (x1, x2))).
    { ii. eapply monotonic_guarantees_eqProp_lifted1 with (unary_op := fun x1 : D1 => f (x1, x2))... eapply f1_isMonotonicMap. }
    assert (f2_preserves_eqProp : forall x1 : D1, preserves_eqProp1 (fun x2 : D2 => f (x1, x2))).
    { ii. eapply monotonic_guarantees_eqProp_lifted1 with (unary_op := fun x2 : D2 => f (x1, x2))... eapply f2_isMonotonicMap. }
    assert (f_preserves_eqProp : preserves_eqProp1 f).
    { intros [x1 x2] [x1' x2'] [? ?]; simpl in *. transitivity (f (x1', x2)); [eapply f1_preserves_eqProp | eapply f2_preserves_eqProp]... }
    intros X X_isDirected. set (X1 := image fst X). set (X2 := image snd X).
    set (image_fst_liftsDirected X X_isDirected) as X1_isDirected. fold X1 in X1_isDirected.
    set (image_snd_liftsDirected X X_isDirected) as X2_isDirected. fold X2 in X2_isDirected.
    assert (mayday : isSupremumOf (getSupremumOf_inCPO X1 X1_isDirected, getSupremumOf_inCPO X2 X2_isDirected) X) by exact (getSupremumOf_inCPO_isSupremum X X_isDirected).
    assert (claim1 : forall x1 : D1, exists sup_X2_x1 : D2, exists sup_f_X2_x1 : D3, isSupremumOf sup_X2_x1 X2 /\ isSupremumOf sup_f_X2_x1 (image (fun x2 : D2 => f (x1, x2)) X2) /\ f (x1, sup_X2_x1) == sup_f_X2_x1).
    { intros x1. eapply the_main_reason_for_introducing_ScottTopology with (f := fun x2 : D2 => f (x1, x2))... }
    assert (claim2 : forall x2 : D2, exists sup_X1_x2 : D1, exists sup_f_X1_x2 : D3, isSupremumOf sup_X1_x2 X1 /\ isSupremumOf sup_f_X1_x2 (image (fun x1 : D1 => f (x1, x2)) X1) /\ f (sup_X1_x2, x2) == sup_f_X1_x2).
    { intros x2. eapply the_main_reason_for_introducing_ScottTopology with (f := fun x1 : D1 => f (x1, x2))... }
    set (sup_X1 := getSupremumOf_inCPO X1 X1_isDirected). fold sup_X1 in mayday.
    set (sup_X2 := getSupremumOf_inCPO X2 X2_isDirected). fold sup_X2 in mayday.
    pose proof (sup_X1_isSupremumOf_X1 := getSupremumOf_inCPO_isSupremum X1 X1_isDirected). fold sup_X1 in sup_X1_isSupremumOf_X1.
    pose proof (sup_X2_isSupremumOf_X2 := getSupremumOf_inCPO_isSupremum X2 X2_isDirected). fold sup_X2 in sup_X2_isSupremumOf_X2.
    assert (claim3 : isSupremumOf (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
    { pose proof (claim1 sup_X1) as [sup_X2_x1 [sup_f_X2_x1 [sup_X2_x1_isSupremum [sup_f_X1_x2_isSupremum H_EQ]]]].
      eapply Supremum_congruence with (sup_X := sup_f_X2_x1).
      - rewrite <- H_EQ. eapply f_preserves_eqProp. split; simpl.
        + reflexivity.
        + eapply Supremum_unique...
      - reflexivity.
      - exact (sup_f_X1_x2_isSupremum).
    }
    assert (claim4 : forall x2 : D2, member x2 X2 -> isSupremumOf (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)).
    { intros x2 x2_in. pose proof (claim2 x2) as [sup_X1' [sup_f_X1_x2' [sup_X1'_isSupremum [sup_f_X1_x2'_isSupremum H_EQ]]]].
      eapply Supremum_congruence with (sup_X := sup_f_X1_x2').
      - rewrite <- H_EQ. eapply f_preserves_eqProp. split; simpl.
        + eapply Supremum_unique...
        + reflexivity.
      - reflexivity.
      - exact (sup_f_X1_x2'_isSupremum).
    }
    assert (claim5 : isSupremumOf (f (sup_X1, sup_X2)) (MapSuprema (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
    { intros upper_bound. split.
      - intros ? sup_Y [Y [Y_in sup_Y_isSupremum]]; desnw. red in sup_Y_isSupremum.
        apply in_image_iff in Y_in. destruct Y_in as [x2 [? x2_in]]; subst Y.
        eapply sup_Y_isSupremum. intros y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [x1 [? x1_in]]; subst y.
        rewrite <- SUPREMUM_LE_UPPER_BOUND. transitivity (f (sup_X1, x2)).
        + eapply f1_isMonotonicMap. eapply sup_X1_isSupremumOf_X1...
        + eapply f2_isMonotonicMap. eapply sup_X2_isSupremumOf_X2...
      - intros ?; desnw. eapply claim3. intros y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [x2 [? x2_in]]; subst y.
        eapply UPPER_BOUND. exists (image (fun x1 : D1 => f (x1, x2)) X1)...
    }
    assert (claim6 : isSupremumOf (f (sup_X1, sup_X2)) (unions (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
    { eapply SupremumOfMapSuprema_isSupremumOf_unions...
      intros Y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [x2 [? x2_in]]; subst Y. exists (f (sup_X1, x2))...
    }
    assert (claim7 : isSupremumOf (f (sup_X1, sup_X2)) (image f X)).
    { intros upper_bound. split.
      - intros ? y ?; desnw. apply in_image_iff in H_IN. destruct H_IN as [[x1 x2] [? H_IN]]; subst y.
        eapply claim6... eapply in_unions_iff. exists (image (fun x1' : D1 => f (x1', x2)) X1). split...
      - ii; desnw. eapply claim6. intros y y_in; unnw.
        apply in_unions_iff in y_in. destruct y_in as [Y [y_in_Y Y_in]].
        apply in_image_iff in Y_in. destruct Y_in as [x2 [? x2_in_X2]]; subst Y.
        apply in_image_iff in y_in_Y. destruct y_in_Y as [x1 [? x1_in_X1]]; subst y.
        apply in_image_iff in x1_in_X1. destruct x1_in_X1 as [[x1_1 x2_1] [? x1_in_X]]; subst x1.
        apply in_image_iff in x2_in_X2. destruct x2_in_X2 as [[x1_2 x2_2] [? x2_in_X]]; subst x2.
        pose proof (proj2 X_isDirected (x1_1, x2_1) x1_in_X (x1_2, x2_2) x2_in_X) as [[x1_3 x2_3] [x3_in [[x1_1_le_x1_3 x2_1_le_x2_3] [x1_2_le_x1_3 x2_2_le_x2_3]]]]; simpl in *. unnw.
        transitivity (f (x1_3, x2_3)).
        + transitivity (f (x1_1, x2_3)); [eapply f2_isMonotonicMap | eapply f1_isMonotonicMap]...
        + eapply UPPER_BOUND...
    }
    intros sup_X1' sup_X2' sup_X1'_isSupremum sup_X2'_isSupremum.
    assert (to_show : f (sup_X1, sup_X2) == f (sup_X1', sup_X2')).
    { eapply f_preserves_eqProp. split; simpl; eapply Supremum_unique... }
    rewrite <- to_show...
  Qed.

  Corollary f_cont_if_f1_and_f2_cont {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} {D3_isCPO : isCPO D3} (f : D1 * D2 -> D3)
    (f1_isContinuousMap : forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2)))
    (f2_isContinuousMap : forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2)))
    : isContinuousMap f.
  Proof with eauto with *.
    assert (f1_isMonotonicMap : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2))).
    { intros x2. eapply ScottContinuousMap_isMonotonicMap... }
    assert (f2_isMonotonicMap : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2))).
    { intros x1. eapply ScottContinuousMap_isMonotonicMap... }
    assert (f1_preserves_eqProp : forall x2 : D2, preserves_eqProp1 (fun x1 : D1 => f (x1, x2))).
    { ii. eapply monotonic_guarantees_eqProp_lifted1 with (unary_op := fun x1 : D1 => f (x1, x2))... eapply f1_isMonotonicMap. }
    assert (f2_preserves_eqProp : forall x1 : D1, preserves_eqProp1 (fun x2 : D2 => f (x1, x2))).
    { ii. eapply monotonic_guarantees_eqProp_lifted1 with (unary_op := fun x2 : D2 => f (x1, x2))... eapply f2_isMonotonicMap. }
    assert (f_preserves_eqProp : preserves_eqProp1 f).
    { intros [x1 x2] [x1' x2'] [? ?]; simpl in *. transitivity (f (x1', x2)); [eapply f1_preserves_eqProp | eapply f2_preserves_eqProp]... }
    eapply the_main_reason_for_introducing_ScottTopology...
    intros X X_isDirected; unnw. set (X1 := image fst X). set (X2 := image snd X).
    set (image_fst_liftsDirected X X_isDirected) as X1_isDirected. fold X1 in X1_isDirected.
    set (image_snd_liftsDirected X X_isDirected) as X2_isDirected. fold X2 in X2_isDirected.
    assert (mayday : isSupremumOf (getSupremumOf_inCPO X1 X1_isDirected, getSupremumOf_inCPO X2 X2_isDirected) X) by exact (getSupremumOf_inCPO_isSupremum X X_isDirected).
    set (sup_X1 := getSupremumOf_inCPO X1 X1_isDirected). fold sup_X1 in mayday.
    set (sup_X2 := getSupremumOf_inCPO X2 X2_isDirected). fold sup_X2 in mayday.
    assert (sup_X1_isSupremumOf_X1 : isSupremumOf sup_X1 X1) by exact (getSupremumOf_inCPO_isSupremum X1 X1_isDirected).
    assert (sup_X2_isSupremumOf_X2 : isSupremumOf sup_X2 X2) by exact (getSupremumOf_inCPO_isSupremum X2 X2_isDirected).
    exists (sup_X1, sup_X2), (f (sup_X1, sup_X2)). split; trivial. split; [eapply f_sup_X1_sup_X2_eq_sup_f_X1_X2 | reflexivity]...
  Qed.

  Theorem seperately_continuous_iff {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} {D3_isCPO : isCPO D3} (f : D1 * D2 -> D3)
    : ⟪ CONT_FST_ARG : forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2)) ⟫ /\ ⟪ CONT_SND_ARG : forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2)) ⟫ <-> isContinuousMap f.
  Proof with eauto.
    split.
    - intros [? ?]; desnw. eapply f_cont_if_f1_and_f2_cont...
    - intros ?; split; [intros x1; eapply f1_cont_if_f_cont | intros x2; eapply f2_cont_if_f_cont]...
  Qed.

  Section SCOTT_APP.

  Context {D1 : Type} {D2 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2}.

  Let scottApp1 : ⟬ D1 ⟶ D2 ⟭ * D1 -> D2 := fun '(f, x) => proj1_sig f x.

  Lemma scottApp1_isMonotonicMap
    : isMonotonicMap scottApp1.
  Proof with eauto with *.
    intros [f1 x1] [f2 x2] [f1_le_f2 x1_le_x2]; simpl in *. transitivity (proj1_sig f1 x2).
    - eapply ScottContinuousMap_isMonotonicMap... exact (proj2_sig f1).
    - clear x1 x1_le_x2. revert x2. change (f1 =< f2)...
  Qed.

  Lemma scottApp1_preserves_eqProp (f1 : ⟬ D1 ⟶ D2 ⟭) (f2 : ⟬ D1 ⟶ D2 ⟭) (x1 : D1) (x2 : D1)
    (f1_eq_f2 : f1 == f2)
    (x1_eq_x2 : x1 == x2)
    : scottApp1 (f1, x1) == scottApp1 (f2, x2).
  Proof.
    transitivity (scottApp1 (f1, x2)).
    - simpl. eapply monotonic_guarantees_eqProp_lifted1; trivial.
      eapply ScottContinuousMap_isMonotonicMap. exact (proj2_sig f1).
    - simpl. clear x1 x1_eq_x2. revert x2. now change (f1 == f2).
  Qed.

  Lemma scottApp1_isContinuousMap
    : isContinuousMap scottApp1.
  Proof with eauto with *.
    eapply f_cont_if_f1_and_f2_cont.
    - intros x. eapply the_main_reason_for_introducing_ScottTopology.
      + ii; eapply scottApp1_preserves_eqProp...
      + intros F F_isDirected. set (Y := image (fun f_i : ⟬ D1 ⟶ D2 ⟭ => scottApp1 (f_i, x)) F). simpl in Y. set (sup_F := getSupremumOf_inCPO F F_isDirected).
        assert (sup_F_isSupremumOf_F : isSupremumOf sup_F F) by exact (getSupremumOf_inCPO_isSupremum F F_isDirected).
        exists (sup_F), (scottApp1 (sup_F, x)). split; trivial. split; [simpl | reflexivity].
        eapply supremumOfScottContinuousMaps_isSupremum.
    - exact (fun f : ⟬ D1 ⟶ D2 ⟭ => proj2_sig f).
  Qed.

  Definition ScottApp : ⟬ ⟬ D1 ⟶ D2 ⟭ * D1 ⟶ D2 ⟭ :=
    @exist (⟬ D1 ⟶ D2 ⟭ * D1 -> D2) isContinuousMap scottApp1 scottApp1_isContinuousMap
  .

  End SCOTT_APP.

  Section SCOTT_LAM.

  Context {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} {D1_isCPO : isCPO D1} {D2_isCPO : isCPO D2} {D3_isCPO : isCPO D3}.

  Let scottLam1 (f : ⟬ D1 * D2 ⟶ D3 ⟭) (x1 : D1) (x2 : D2) : D3 := proj1_sig f (x1, x2).

  Let scottLam2 (f : ⟬ D1 * D2 ⟶ D3 ⟭) (x1 : D1) : ⟬ D2 ⟶ D3 ⟭ := @exist (D2 -> D3) isContinuousMap (scottLam1 f x1) (f2_cont_if_f_cont (proj1_sig f) x1 (proj2_sig f)).

  Lemma scottLam2_isContinuousMap (f : ⟬ D1 * D2 ⟶ D3 ⟭)
    : isContinuousMap (scottLam2 f).
  Proof with eauto with *.
    assert (f_isMonotonicMap : isMonotonicMap (proj1_sig f)).
    { eapply ScottContinuousMap_isMonotonicMap. exact (proj2_sig f). }
    pose proof (proj2 (seperately_monotonic_iff_monotonic (proj1_sig f)) f_isMonotonicMap) as [? ?]; desnw.
    assert (scottLam2_f_isMonotonicMap : isMonotonicMap (scottLam2 f)).
    { intros x1 x1' x1_le_x1' x2. simpl. unfold scottLam1. eapply MON_FST_ARG... }
    assert (scottLam2_f_preserves_eqProp : preserves_eqProp1 (scottLam2 f)).
    { ii. eapply leProp_Antisymmetric; eapply scottLam2_f_isMonotonicMap... }
    eapply the_main_reason_for_introducing_ScottTopology; trivial.
    intros X1 X1_isDirected; unnw. set (sup_X1 := getSupremumOf_inCPO X1 X1_isDirected).
    assert (Y_isDirected : isDirected (image (scottLam2 f) X1)).
    { eapply preservesDirected_if_isMonotonicMap... }
    set (Y := image (scottLam2 f) X1). fold Y in Y_isDirected. set (sup_Y := getSupremumOf_inCPO Y Y_isDirected).
    assert (sup_X1_isSupremumOf_X1 : isSupremumOf sup_X1 X1) by exact (getSupremumOf_inCPO_isSupremum X1 X1_isDirected).
    assert (sup_Y_isSupremumOf_Y : isSupremumOf sup_Y Y) by exact (getSupremumOf_inCPO_isSupremum Y Y_isDirected).
    exists (sup_X1), (sup_Y). split; trivial. split; trivial.
    assert (claim1 : forall x1 : D1, member x1 X1 -> forall x2 : D2, proj1_sig f (x1, x2) =< proj1_sig f (sup_X1, x2)).
    { intros x1 x1_in_X1 x2. eapply f_isMonotonicMap. split; [eapply sup_X1_isSupremumOf_X1 | reflexivity]... }
    intros x2. simpl. unfold scottLam1. pose proof (f_sup_X1_x2_eq_sup_f_X1_x2 (proj1_sig f) x2 X1 sup_X1 (proj2_sig f) X1_isDirected sup_X1_isSupremumOf_X1) as claim2.
    eapply Supremum_unique.
    - exact (claim2).
    - eapply supremumOfScottContinuousMaps_isSupremum.
    - intros z. split.
      + intros z_in. apply in_image_iff in z_in. destruct z_in as [x1 [? x1_in_X1]]; subst z...
      + intros z_in. apply in_image_iff in z_in. destruct z_in as [f1 [? f1_in_Y]]; subst z. apply in_image_iff in f1_in_Y. destruct f1_in_Y as [x1 [? x1_in_X1]]; subst f1...
  Qed.

  Let scottLam3 (f : ⟬ D1 * D2 ⟶ D3 ⟭) : ⟬ D1 ⟶ ⟬ D2 ⟶ D3 ⟭ ⟭ := @exist (D1 -> ⟬ D2 ⟶ D3 ⟭) isContinuousMap (scottLam2 f) (scottLam2_isContinuousMap f).

  End SCOTT_LAM.

End BasicCpoTheory.
