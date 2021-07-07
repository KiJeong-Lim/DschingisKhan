Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import DschingisKhan.theories.Auxiliary.
Require Import DschingisKhan.theories.ConstructiveTheory.

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

  Local Program Instance ContinuousMap_isPoset {A : Type} {B : Type} (A_requiresTopologicalSpace : isTopologicalSpace A) (B_requiresTopologicalSpace : isTopologicalSpace B) (B_requiresPoset : isPoset B) : isPoset (A >=> B) :=
    { leProp :=
      fun f1 : A >=> B =>
      fun f2 : A >=> B =>
      forall x : A,
      proj1_sig' f1 x =< proj1_sig' f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with firstorder with my_hints.
    intros f1 f2...
  Qed.

  Definition fish_isMonotonic {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : (D >=> D') -> (D >~> D') :=
    fun f : D >=> D' =>
    exist isMonotonicMap (proj1_sig' f) (ContinuousMapOnCpos_isMonotonic (proj1_sig' f) (proj2_sig' f))
  .

  Global Instance fish_isSetoid {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isSetoid (D >=> D') :=
    ContinuousMap_isSetoid (ScottTopology_isTopologicalSpace D_requiresCompletePartialOrder) (ScottTopology_isTopologicalSpace D'_requiresCompletePartialOrder) (@Poset_requiresSetoid D' (@CompletePartialOrder_requiresPoset D' D'_requiresCompletePartialOrder))
  .

  Global Instance fish_isPoset {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isPoset (D >=> D') :=
    ContinuousMap_isPoset (ScottTopology_isTopologicalSpace D_requiresCompletePartialOrder) (ScottTopology_isTopologicalSpace D'_requiresCompletePartialOrder) (@CompletePartialOrder_requiresPoset D' D'_requiresCompletePartialOrder)
  .

  Lemma sup_of_set_of_fishes_is_well_defined {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall F : ensemble (D >=> D'),
    isDirected F ->
    forall x : D,
    isDirected (image (fun f_i : D >=> D' => proj1_sig' f_i x) F).
  Proof with eauto with *.
    intros fs [H H0] x.
    split.
    - destruct H as [f0].
      exists (proj1_sig' f0 x).
      apply (in_image (fun f : D >=> D' => proj1_sig' f x))...
    - intros y1 H1 y2 H2.
      inversion H1; subst.
      inversion H2; subst.
      rename x0 into f1, x1 into f2.
      destruct (H0 f1 H3 f2 H4) as [f3 [H5 [H6 H7]]].
      exists (proj1_sig' f3 x).
      repeat split...
      apply (in_image (fun f : D >=> D' => proj1_sig' f x))...
  Qed.

  Lemma sup_of_set_of_fishes_exists_if_it_is_directed {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall F : ensemble (D >=> D'),
    forall F_isDirected : isDirected F,
    let f : D -> D' := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x)) in
    isContinuousMap f.
  Proof with eauto with *.
    intros F F_isDirected f.
    assert (H : isMonotonicMap f).
    { intros x1 x2 H.
      unfold f.
      destruct (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x1) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x1)) as [sup_F1_x H0].
      destruct (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x2) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x2)) as [sup_F2_x H1].
      simpl.
      apply H0.
      intros x' H2.
      inversion H2; subst.
      rename x into f_i.
      transitivity (proj1_sig' f_i x2).
      - apply (ContinuousMapOnCpos_isMonotonic)...
        apply (proj2_sig' f_i).
      - apply H1...
        apply (in_image (fun f_i' : D >=> D' => proj1_sig' f_i' x2))...
    }
    apply (the_main_reason_for_introducing_ScottTopology (exist isMonotonicMap f H)).
    unfold characterization_of_ContinuousMap_on_cpos.
    simpl.
    intros X H0.
    set (Y := image f X).
    destruct (square_up_exists X H0) as [sup_X H1].
    assert ( claim1 :
      forall f_i : D >=> D',
      member f_i F ->
      isSupremum (proj1_sig' f_i sup_X) (image (fun x : D => proj1_sig' f_i x) X)
    ).
    { intros f_i H2.
      assert (H3 : isContinuousMap (proj1_sig' f_i)) by apply (proj2_sig' f_i).
      assert (H4 : characterization_of_ContinuousMap_on_cpos (proj1_sig' f_i)).
      { apply (the_main_reason_for_introducing_ScottTopology (fish_isMonotonic f_i)).
        apply (proj2_sig' f_i).
      }
      destruct (H4 X H0) as [sup_X' [sup_Y' [H5 [H6 H7]]]].
      assert (H8 : sup_X' == sup_X) by now apply (isSupremum_unique X).
      apply (proj2 (isSupremum_unique (image (fun x : D => proj1_sig' f_i x) X) _ H6 (proj1_sig' f_i sup_X))).
      assert (H9 : proj1_sig' f_i sup_X' == proj1_sig' f_i sup_X).
      { apply (MonotonicMap_preservesSetoid (proj1_sig' f_i))...
        apply (proj2_sig (fish_isMonotonic f_i)).
      }
      transitivity (proj1_sig' f_i sup_X')...
    }
    assert (claim2 : isSupremum (f sup_X) (image (fun f_i : D >=> D' => proj1_sig' f_i sup_X) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i sup_X) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected sup_X))).
    assert (claim3 : isSupremum (f sup_X) (unions (image (fun f_i : D >=> D' => image (fun x : D => proj1_sig' f_i x) X) F))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs.
      - intros ys H2.
        inversion H2; subst.
        rename x into f_i.
        exists (proj1_sig' f_i sup_X)...
      - intros y.
        split.
        + intros H2 y' [ys [H3 H4]].
          inversion H3; subst.
          rename x into f_i.
          assert (H6 := claim1 f_i H5).
          assert (H7 : y' == proj1_sig' f_i sup_X) by now apply (isSupremum_unique (image (fun x : D => proj1_sig' f_i x) X)).
          transitivity (proj1_sig' f_i sup_X)...
          apply claim2...
          apply (in_image (fun f_i0 : D >=> D' => proj1_sig' f_i0 sup_X))...
        + intros H2.
          apply claim2.
          intros y' H3.
          inversion H3; subst.
          rename x into f_i.
          apply H2.
          exists (image (fun x : D => proj1_sig' f_i x) X).
          split...
          apply (in_image (fun f_i0 : D >=> D' => image (fun x : D => proj1_sig' f_i0 x) X))...
    }
    assert (claim4 : isSupremum (f sup_X) (unions (image (fun x : D => image (fun f_i : D >=> D' => proj1_sig' f_i x) F) X))).
    { enough (H2 : forall x' : D', member x' (unions (image (fun f_i : D >=> D' => image (fun x : D => proj1_sig' f_i x) X) F)) <-> member x' (unions (image (fun x : D => image (fun f_i : D >=> D' => proj1_sig' f_i x) F) X))) by now apply (proj2 (isSupremum_ext _ _ H2 _ claim3 _) (Setoid_refl (f sup_X))).
      intros y.
      split.
      - intros H2.
        inversion H2; subst.
        rename xs into ys.
        inversion H4; subst.
        rename x into f_i.
        inversion H3; subst.
        apply (in_unions (image (fun f_i' : D >=> D' => proj1_sig' f_i' x) F)).
        + apply (in_image (fun f_i' : D >=> D' => proj1_sig' f_i' x))...
        + apply (in_image (fun x0 : D => image (fun f_i0 : D >=> D' => proj1_sig' f_i0 x0) F))...
      - intros H2.
        inversion H2; subst.
        rename xs into ys.
        inversion H4; subst.
        inversion H3; subst.
        rename x0 into f_i.
        apply (in_unions (image (fun x' : D => proj1_sig' f_i x') X)).
        + apply (in_image (fun x' : D => proj1_sig' f_i x'))...
        + apply (in_image (fun f_i0 : D >=> D' => image (fun x0 : D => proj1_sig' f_i0 x0) X))...
    }
    assert (claim5 : isSupremum (f sup_X) (image_sup (image (fun x : D => image (fun f_i : D >=> D' => proj1_sig' f_i x) F) X))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
      intros ys H2.
      inversion H2; subst.
      exists (f x).
      intros y.
      split.
      - intros H4 y' H5.
        inversion H5; subst.
        rename x0 into f_i.
        apply (proj2_sig (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x)))...
      - intros H4.
        assert (H5 : isSupremum (f x) (image (fun f_i : D >=> D' => proj1_sig' f_i x) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x))).
        apply H5...
    }
    assert (claim6 : isSupremum (f sup_X) (image f X)).
    { intros y.
      split.
      - intros H2 y' H3.
        inversion H3; subst.
        apply claim5...
        exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F).
        split.
        + apply (in_image (fun x0 : D => image (fun f_i : D >=> D' => proj1_sig' f_i x0) F))...
        + apply (proj2_sig (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x))).
      - intros H2.
        apply claim5.
        intros y' [ys [H3 H4]].
        inversion H3; subst.
        assert (H6 : isSupremum (f x) (image (fun f_i : D >=> D' => proj1_sig' f_i x) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x))).
        assert (H7 : y' == f x) by now apply (isSupremum_unique (image (fun f_i : D >=> D' => proj1_sig' f_i x) F)).
        transitivity (f x)...
    }
    exists sup_X, (f sup_X)...
  Qed.

  Definition sup_of_set_of_fishes {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : forall F : ensemble (D >=> D'), isDirected F -> (D >=> D') :=
    fun F : ensemble (D >=> D') =>
    fun F_isDirected : isDirected F =>
    exist' (fun x : D => proj1_sig (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x))) (sup_of_set_of_fishes_exists_if_it_is_directed F F_isDirected)
  .

  Lemma sup_of_set_of_fishes_isSupremum {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall F : ensemble (D >=> D'),
    forall F_isDirected : isDirected F,
    isSupremum (sup_of_set_of_fishes F F_isDirected) F.
  Proof with eauto with *.
    intros F F_isDirected f.
    split.
    - intros H f' H0.
      assert (H1 : forall x : D, proj1_sig' f' x =< proj1_sig' (sup_of_set_of_fishes F F_isDirected) x).
      { intros x.
        unfold sup_of_set_of_fishes.
        simpl.
        destruct (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x)) as [sup_F_x H1].
        simpl.
        apply H1...
        apply (in_image (fun f_i : D >=> D' => proj1_sig' f_i x))...
      }
      transitivity (sup_of_set_of_fishes F F_isDirected)...
    - intros H x.
      unfold sup_of_set_of_fishes.
      simpl.
      destruct (square_up_exists (image (fun f_i : D >=> D' => proj1_sig' f_i x) F) (sup_of_set_of_fishes_is_well_defined F F_isDirected x)) as [sup_F_x H0].
      simpl.
      apply H0.
      intros f' H1.
      inversion H1; subst.
      rename x0 into f_i.
      apply H...
  Qed.

  Lemma bot_of_fishes_isContinuous {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompleteLattice : isCompletePartialOrder D'} :
    isContinuousMap (fun _ : D => proj1_sig bottom_exists).
  Proof with eauto with *.
    intros Y [H H0].
    split.
    - intros x1 x2 H1 H2.
      inversion H1; subst.
      apply (in_preimage (fun _ : D => proj1_sig bottom_exists))...
    - intros X [[x_0 H1] H2] sup_X H3 H4.
      inversion H4; subst.
      exists x_0.
      constructor...
  Qed.

  Definition bot_of_fishes {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : D >=> D' :=
    exist' (fun _ : D => proj1_sig (@bottom_exists D' D'_isCompletePartialOrder)) bot_of_fishes_isContinuous
  .

  Lemma bot_of_fishes_isBottom {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D >=> D',
    bot_of_fishes =< f.
  Proof with eauto with *.
    unfold bot_of_fishes.
    intros f x.
    simpl.
    destruct bottom_exists as [bot_D' H].
    simpl...
  Qed.

  Global Instance fish_isCompletePartialOrder {D : Type} {D' : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) (D'_requiresCompletePartialOrder : isCompletePartialOrder D') : isCompletePartialOrder (D >=> D') :=
    { CompletePartialOrder_requiresPoset := fish_isPoset D_requiresCompletePartialOrder D'_requiresCompletePartialOrder
    ; bottom_exists := exist _ bot_of_fishes bot_of_fishes_isBottom
    ; square_up_exists :=
      fun F : ensemble (D >=> D') =>
      fun F_isDirected : isDirected F =>
      exist _ (sup_of_set_of_fishes F F_isDirected) (sup_of_set_of_fishes_isSupremum F F_isDirected)
    }
  .

End ClassicalDomainTheory.
