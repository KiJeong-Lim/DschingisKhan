Require Import Coq.Lists.List.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeClassic.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BasicGeneralTopology.
Require Import DschingisKhan.Logic.ScottTopology.

Module BasicCpoTheory.

  Import ListNotations MathProps MathClasses BasicPosetTheory BasicGeneralTopology DomainTheoryHelper ScottTopology ExclusiveMiddle.

  Definition ScottContinuousMaps (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : Type :=
    @sig (Hask.arrow dom cod) (isContinuousMap (dom_isTopology := TopologyOfDanaScott dom) (cod_isTopology := TopologyOfDanaScott cod))
  .

  Local Instance ScottContinuousMaps_asPoset (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : isPoset (ScottContinuousMaps dom cod) :=
    subPoset (Hask.arrow dom cod) (requiresPoset := arrow_isPoset dom cod)
  .

  Local Notation " ⟬ dom ⟶ cod ⟭ " := (ScottContinuousMaps dom cod) : type_scope.

  Definition U {D : Type} {D_isPoset : isPoset D} (x : D) : ensemble D :=
    fun z : D => ~ z =< x
  .

  Lemma U_x_isOpen {D : Type} {D_isPoset : isPoset D} (x : D)
    : isOpen (U x).
  Proof. (* Thanks to Junyoung Jang *)
    split.
    - intros y z y_in_U_x y_le_z z_le_x. unnw. contradiction y_in_U_x. now transitivity (z).
    - intros X [X_nonempty X_isDirected] sup_X sup_X_isSupremumOf_X sup_X_in_U_x. unnw.
      assert (NOT_UPPER_BOUND : ~ << UPPER_BOUND : forall z : D, member z X -> z =< x >>).
      { ii; desnw. contradiction sup_X_in_U_x. now eapply sup_X_isSupremumOf_X. }
      eapply NNPP. intros H_false. contradiction NOT_UPPER_BOUND. intros y y_in_X.
      eapply NNPP. intros y_in_U_x. contradiction H_false. now exists (y).
  Qed.

  Lemma ScottContinuousMap_isMonotonicMap {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (f : dom -> cod)
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

  Lemma f_sup_X_eq_sup_image_f_X {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCPO : isCPO dom} {cod_isCPO : isCPO cod} (f : dom -> cod) (X : ensemble dom) (sup_X : dom)
    (f_isContinuousMap : isContinuousMap f)
    (X_isDirected : isDirected X)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    (image_f_X_isDirected : isDirected (image f X))
    : f sup_X == proj1_sig (getSupremumOf_inCPO (image f X) image_f_X_isDirected).
  Proof with eauto with *.
    assert (f_isMonotonicMap : isMonotonicMap f) by now eapply ScottContinuousMap_isMonotonicMap.
    revert image_f_X_isDirected. keep (image f X) as Y into (ensemble cod). fold Y. ii.
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
    eapply @leProp_Antisymmetric with (requiresPoset := cod_isPoset)...
  Qed.

  Lemma sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y  {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCPO : isCPO dom} {cod_isCPO : isCPO cod} (f : dom -> cod) (X : ensemble dom) (sup_X : dom) (sup_Y : cod)
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

  Corollary ScottContinuousMap_preservesSupremum {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCPO : isCPO dom} {cod_isCPO : isCPO cod} (f : dom -> cod) (X : ensemble dom) (sup_X : dom)
    (f_isContinuousMap : isContinuousMap f)
    (X_isDirected : isDirected X)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : isSupremumOf (f sup_X) (image f X).
  Proof. eapply sup_Y_isSupremumOf_image_f_X_iff_f_sup_X_eq_sup_Y; eauto with *. Qed.

  Definition preservesSupremum {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (f : dom -> cod) : Prop :=
    forall X : ensemble dom, isDirected X -> exists sup_X : dom, exists sup_Y : cod, isSupremumOf sup_X X /\ isSupremumOf sup_Y (image f X) /\ f sup_X == sup_Y
  .

  Lemma isMonotonicMap_if_preservesSupremum {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCPO : isCPO dom} {cod_isCPO : isCPO cod} (f : dom -> cod)
    (f_preserves_eqProp : preserves_eqProp1 f)
    (f_preservesSupremum : preservesSupremum f)
    : isMonotonicMap f.
  Proof.
    intros x1 x2 x1_le_x2.
    keep (finite [x1; x2]) as X into (ensemble dom).
    keep (image f X) as Y into (ensemble cod).
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

  Lemma liftsDirected_if_preservesSupremum {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCPO : isCPO dom} {cod_isCPO : isCPO cod} (f : dom -> cod)
    (f_preserves_eqProp : preserves_eqProp1 f)
    (f_preservesSupremum : preservesSupremum f)
    : forall X : ensemble dom, << DIRECTED : isDirected X >> -> isDirected (image f X).
  Proof with eauto with *.
    pose proof (isMonotonicMap_if_preservesSupremum f f_preserves_eqProp f_preservesSupremum) as claim1.
    ii; desnw. inversion DIRECTED. desnw. split.
    - exists (f x0)...
    - intros y1 ? y2 ?; desnw. apply in_image_iff in H_IN1, H_IN2.
      destruct H_IN1 as [x1 [y1_eq_f_x1 x1_in_X]], H_IN2 as [x2 [y1_eq_f_x2 x2_in_X]]; subst y1 y2.
      pose proof (DIRECTED_OR_EMPTY x1 x1_in_X x2 x2_in_X) as [x3 [x3_in_X [? ?]]]; unnw.
      exists (f x3); split...
  Qed.

  Theorem the_main_reason_for_introducing_ScottTopology {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCPO : isCPO dom} {cod_isCPO : isCPO cod} (f : dom -> cod)
    (f_preserves_eqProp : preserves_eqProp1 f)
    : isContinuousMap f <-> preservesSupremum f.
  Proof with eauto with *.
    split; [intros f_isContinuousMap | intros f_preservesSupremum].
    - intros X X_isDirected. keep (image f X) as Y into (ensemble cod). fold Y.
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
        assert (claim1 : exists y : cod, member y (image f X) /\ member y Y).
        { eapply LIMIT... }
        destruct claim1 as [y [y_in_image_f_X y_in_Y]].
        inversion y_in_image_f_X; subst y.
        exists (x). split... econstructor...
  Qed.

End BasicCpoTheory.
