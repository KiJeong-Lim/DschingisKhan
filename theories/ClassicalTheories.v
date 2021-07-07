Require Import Coq.Logic.Classical.
Require Import DschingisKhan.theories.Auxiliary.
Require Import DschingisKhan.theories.ConstructiveTheories.

Module ClassicalDomainTheory.

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

End ClassicalDomainTheory.
