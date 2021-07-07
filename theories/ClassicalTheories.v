Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import DschingisKhan.theories.Auxiliary.
Require Import DschingisKhan.theories.ConstructiveTheories.

Module ClassicalDomainTheory.

  Import ListNotations.

  Import MyStructures.

  Import DomainTheory.

  Definition U {D : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} : D -> ensemble D :=
    fun x : D =>
    fun z : D =>
    ~ z =< x
  .

  Global Hint Unfold U : my_hints.

  Lemma U_x_isOpen {D : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} :
    forall x : D,
    isOpen (U x).
  Proof with eauto with *.
    intros x.
    assert ( claim1 :
      forall y : D,
      forall z : D,
      member y (U x) ->
      y =< z ->
      member z (U x)
    ).
    { intros y z H H0 H1.
      contradiction H...
    }
    split...
    intros X H sup_X H0 H1.
    inversion H; subst.
    assert (claim2 : ~ (forall x0 : D, x0 =< x \/ ~ member x0 X)).
    { intros H4.
      contradiction H1.
      apply (proj2 (H0 x)).
      intros x0 H5.
      destruct (H4 x0); [apply H6 | contradiction].
    }
    apply not_all_ex_not in claim2.
    destruct claim2 as [x1 H4].
    exists x1.
    apply not_or_and in H4.
    destruct H4 as [H4 H5].
    apply NNPP in H5...
  Qed.

  Lemma ContinuousMapOnCpos_isMonotonic {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f ->
    isMonotonicMap f.
  Proof with eauto with *.
    intros f H x1 x2 H0.
    apply NNPP.
    intros H1.
    assert (H2 : member (f x1) (U (f x2))) by now unfold U.
    assert (H3 : member x1 (preimage f (U (f x2)))) by now constructor.
    assert (H4 : isOpen (preimage f (U (f x2)))) by now apply H, U_x_isOpen.
    assert (H5 : member x2 (preimage f (U (f x2)))) by now apply (proj1 H4 x1 x2).
    enough (H6 : member (f x2) (U (f x2)))...
    inversion H5...
  Qed.

  Lemma ContinuousMapOnCpos_preservesDirected {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    isDirected (image f X).
  Proof with eauto with *.
    intros f H X [[x0 H0] H1].
    assert (H2 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMapOnCpos_isMonotonic.
    split.
    - exists (f x0)...
    - intros y1 H3 y2 H4.
      inversion H3; subst.
      rename x into x1.
      inversion H4; subst.
      rename x into x2.
      destruct (H1 x1 H5 x2 H6) as [x3 [H7 [H8 H9]]].
      exists (f x3).
      split...
  Qed.

  Lemma ContinuousMaps_preservesSupremum {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    isDirected (image f X) ->
    {sup_Y : D' | isSupremum sup_Y (image f X) /\ f sup_X == sup_Y}.
  Proof with eauto with *.
    intros f H X H0 sup_X H1 H2.
    set (Y := image f X).
    assert (H3 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMapOnCpos_isMonotonic.
    destruct (square_up_exists Y H2) as [sup_Y H4].
    exists sup_Y.
    assert (claim1 : sup_Y =< f sup_X).
    { apply H4.
      intros y H5.
      inversion H5; subst.
      apply H3, H1...
    }
    assert (claim2 : f sup_X =< sup_Y).
    { apply NNPP.
      intros H5.
      assert (H6 : member (f sup_X) (U sup_Y)) by now unfold U.
      assert (H7 : member sup_X (preimage f (U sup_Y))) by now constructor.
      assert (H8 : isOpen (preimage f (U sup_Y))) by now apply H, U_x_isOpen.
      destruct H8.
      destruct (H9 X H0 sup_X H1 H7) as [x1 H10].
      inversion H10; subst.
      inversion H12; subst.
      contradiction H13...
    }
    split...
  Qed.

  Definition characterization_of_ContinuousMap_on_cpos {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : (D -> D') -> Prop :=
    fun f : D -> D' =>
    forall X : ensemble D,
    isDirected X ->
    let Y : ensemble D' := image f X in
    exists sup_X : D, exists sup_Y : D', isSupremum sup_X X /\ isSupremum sup_Y Y /\ f sup_X == sup_Y
  .

  Theorem the_main_reason_for_introducing_ScottTopology {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D >~> D',
    isContinuousMap (proj1_sig f) <-> characterization_of_ContinuousMap_on_cpos (proj1_sig f).
  Proof with eauto with *.
    assert (claim1 : forall f : D >~> D', isContinuousMap (proj1_sig f) -> forall x1 : D, forall x2 : D, x1 =< x2 -> proj1_sig f x1 =< proj1_sig f x2).
    { intros f.
      apply (ContinuousMapOnCpos_isMonotonic (proj1_sig f)).
    }
    split.
    - intros H X H0.
      inversion H0; subst.
      set (Y := image (proj1_sig f) X).
      assert (H3 : isDirected Y) by now apply ContinuousMapOnCpos_preservesDirected.
      destruct (square_up_exists X H0) as [sup_X H4].
      exists sup_X.
      destruct (ContinuousMaps_preservesSupremum (proj1_sig f) H X H0 sup_X H4 H3) as [sup_Y H5].
      exists sup_Y...
    - intros H.
      assert (claim2 : forall x1 : D, forall x2 : D, x1 =< x2 -> proj1_sig f x1 =< proj1_sig f x2).
      { intros x1 x2 H0.
        set (X := finite [x1; x2]).
        set (Y := image (proj1_sig f) X).
        assert (H1 : isSupremum x2 X).
        { intros x.
          split.
          - intros H1 x' H2.
            inversion H2; subst.
            destruct H3 as [H3 | [H3 | []]]; subst...
          - intros H1...
        }
        assert (H2 : isDirected X).
        { split.
          - exists x1...
          - intros x1' H2 x2' H3.
            exists x2.
            enough (x1' =< x2 /\ x2' =< x2)...
        }
        destruct (H X H2) as [sup_X H3].
        destruct H3 as [sup_Y [H3 [H4 H5]]].
        assert (H6 : sup_X == x2) by now apply (isSupremum_unique X).
        apply (proj2_sig f)...
      }
      intros O H0.
      split.
      + intros x1 x2 H1 H2.
        inversion H1; subst.
        constructor.
        apply (proj1 H0 (proj1_sig f x1) (proj1_sig f x2))...
      + intros X H1 sup_X H2 H3.
        destruct (H X H1) as [sup_X' [sup_Y [H4 [H5 H6]]]].
        assert (H7 : sup_X == sup_X') by now apply (isSupremum_unique X).
        assert (H8 : member (proj1_sig f sup_X) O) by now inversion H3; subst.
        assert (H9 : isDirected (image (proj1_sig f) X)).
        { destruct H1 as [[x1_0 H1] H9].
          split.
          - exists (proj1_sig f x1_0)...
          - intros y1 H10 y2 H11.
            inversion H10; subst.
            inversion H11; subst.
            rename x into x1, x0 into x2.
            destruct (H9 x1 H12 x2 H13) as [x3 [H14 [H15 H16]]].
            exists (proj1_sig f x3).
            repeat split...
        }
        assert (H10 : nonempty (intersection (image (proj1_sig f) X) O)).
        { apply (proj2 H0 (image (proj1_sig f) X) H9 (proj1_sig f sup_X))...
          assert (H10 : sup_Y == proj1_sig f sup_X).
          { transitivity (proj1_sig f sup_X').
            - symmetry...
            - apply Poset_asym; apply (proj2_sig f)...
          }
          apply (isSupremum_unique (image (proj1_sig f) X) _ H5)...
        }
        destruct H10 as [y1 H10].
        inversion H10; subst.
        inversion H11; subst.
        exists x...
  Qed.

  Inductive sig' {A : Type} : (A -> Prop) -> Type :=
  | exist' {P : A -> Prop} :
    forall x : A,
    P x ->
    sig' P
  .

  Global Hint Constructors sig' : my_hints.

  Definition proj1_sig' {A : Type} {P : A -> Prop} : sig' P -> A :=
    fun sig'_P : sig' P =>
    match sig'_P with
    | exist' x H => x
    end 
  .

  Definition proj2_sig' {A : Type} {P : A -> Prop} : forall sig'_P : sig' P, P (proj1_sig' sig'_P) :=
    fun sig'_P : sig' P =>
    match sig'_P with
    | exist' x H => H
    end 
  .

  Global Notation "D1 >=> D2" := (@sig' (D1 -> D2) isContinuousMap) (at level 25, no associativity) : type_scope.

  

End ClassicalDomainTheory.
