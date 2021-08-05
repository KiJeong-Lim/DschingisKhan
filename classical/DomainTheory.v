Require Import Coq.Lists.List.
Require Import DschingisKhan.classical.MyAxioms.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.DomainTheory.

Module ClassicalCpoTheory.

  Import ListNotations BasicSetoidTheory MyEnsemble BasicPosetTheory BasicTopology ConstructiveCpoTheory.

  Definition U {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D :=
    fun x : D =>
    fun z : D =>
    ~ z =< x
  .

  Global Hint Unfold U : my_hints.

  Lemma U_x_isOpen {D : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} :
    forall x : D,
    isOpen (U x).
  Proof with eauto with *. (* Thanks to Clare Jang *)
    assert ( claim1 :
      forall x : D,
      forall y : D,
      forall z : D,
      member y (U x) ->
      y =< z ->
      member z (U x)
    ).
    { intros x y z H H0 H1.
      contradiction H...
    }
    intros x.
    split...
    intros X H sup_X H0 H1.
    inversion H; subst.
    assert (claim2 : ~ (forall x0 : D, x0 =< x \/ ~ member x0 X)).
    { intros H4.
      contradiction H1.
      apply (proj2 (H0 x)).
      intros x0 H5.
      destruct (H4 x0) as [H6 | H6]; [apply H6 | contradiction].
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
    assert (H6 : member (f x2) (U (f x2))) by now inversion H5...
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
      repeat split...
  Qed.

  Lemma square_up_image {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    forall H2 : isDirected (image f X),
    f sup_X == proj1_sig (square_up_exists (image f X) H2).
  Proof with eauto with *.
    intros f H X H0 sup_X H1 H2.
    set (Y := image f X).
    assert (H3 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMapOnCpos_isMonotonic.
    destruct (square_up_exists Y H2) as [sup_Y H4].
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
      destruct H8 as [H8 H9].
      destruct (H9 X H0 sup_X H1 H7) as [x1 H10].
      inversion H10; subst.
      inversion H12; subst.
      contradiction H13...
    }
    apply Poset_asym...
  Qed.

  Definition ContinuousMaps_preservesSupremum {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    isDirected (image f X) ->
    {sup_Y : D' | isSupremum sup_Y (image f X) /\ f sup_X == sup_Y}.
  Proof.
    intros f H X H0 sup_X H1 H2.
    destruct (square_up_exists (image f X) H2) as [sup_Y H4] eqn: H5.
    exists sup_Y.
    split.
    - exact H4.
    - assert (H6 := square_up_image f H X H0 sup_X H1 H2).
      rewrite H5 in H6.
      exact H6.
  Defined.

  Definition characterization_of_ContinuousMap_on_cpos {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : (D -> D') -> Prop :=
    fun f : D -> D' =>
    forall X : ensemble D,
    isDirected X ->
    let Y : ensemble D' := image f X in
    exists sup_X : D, exists sup_Y : D', isSupremum sup_X X /\ isSupremum sup_Y Y /\ f sup_X == sup_Y
  .

  Theorem the_main_reason_for_introducing_ScottTopology {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D >=> D',
    isContinuousMap (proj1_sig f) <-> characterization_of_ContinuousMap_on_cpos (proj1_sig f).
  Proof with eauto with *.
    assert (claim1 : forall f : D >=> D', isContinuousMap (proj1_sig f) -> forall x1 : D, forall x2 : D, x1 =< x2 -> proj1_sig f x1 =< proj1_sig f x2) by apply (fun f : D >=> D' => ContinuousMapOnCpos_isMonotonic (proj1_sig f)).
    split.
    - intros H X H0.
      inversion H0; subst.
      set (Y := image (proj1_sig f) X).
      assert (H3 : isDirected Y) by now apply ContinuousMapOnCpos_preservesDirected.
      destruct (square_up_exists X H0) as [sup_X H4].
      destruct (ContinuousMaps_preservesSupremum (proj1_sig f) H X H0 sup_X H4 H3) as [sup_Y H5].
      exists sup_X, sup_Y...
    - intros H.
      assert (claim2 : forall x1 : D, forall x2 : D, x1 =< x2 -> proj1_sig f x1 =< proj1_sig f x2).
      { intros x1 x2 H0.
        set (X := finite [x1; x2]).
        set (Y := image (proj1_sig f) X).
        assert (claim2_aux1 : isSupremum x2 X).
        { intros x.
          split.
          - intros H1 x' H2.
            inversion H2; subst.
            destruct H3 as [H3 | [H3 | []]]; subst...
          - intros H1...
        }
        assert (claim2_aux2 : isDirected X).
        { split.
          - exists x1...
          - intros x1' H1 x2' H2.
            exists x2.
            enough (H4 : x1' =< x2 /\ x2' =< x2)...
        }
        destruct (H X claim2_aux2) as [sup_X [sup_Y [H1 [H2 H3]]]].
        assert (H4 : sup_X == x2) by now apply (isSupremum_unique X).
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
        assert (claim3 : isDirected (image (proj1_sig f) X)).
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
        assert (claim4 : nonempty (intersection (image (proj1_sig f) X) O)).
        { apply (proj2 H0 (image (proj1_sig f) X) claim3 (proj1_sig f sup_X))...
          assert (claim4_aux1 : sup_Y == proj1_sig f sup_X).
          { transitivity (proj1_sig f sup_X').
            - symmetry...
            - apply Poset_asym; apply (proj2_sig f)...
          }
          apply (isSupremum_unique (image (proj1_sig f) X) _ H5)...
        }
        destruct claim4 as [y1 H9].
        inversion H9; subst.
        inversion H10; subst.
        exists x...
  Qed.

  Local Instance ContinuousMap_isPoset {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) (D'_requiresCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset) : isPoset (@sig (D -> D') (@isContinuousMap D D' (ScottTopology D_requiresCompletePartialOrder) (ScottTopology D'_requiresCompletePartialOrder))) :=
    @SubPoset (D -> D') (@isContinuousMap D D' (ScottTopology D_requiresCompletePartialOrder) (ScottTopology D'_requiresCompletePartialOrder)) (arrow_isPoset D'_isPoset)
  .

  Definition squig_isMonotonic {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : (D ~> D') -> (D >=> D') :=
    fun f : D ~> D' =>
    exist isMonotonicMap (proj1_sig f) (ContinuousMapOnCpos_isMonotonic (proj1_sig f) (proj2_sig f))
  .

  Lemma sup_of_set_of_squigs_is_well_defined {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall F : ensemble (D ~> D'),
    isDirected F ->
    forall x : D,
    isDirected (image (fun f_i : D ~> D' => proj1_sig f_i x) F).
  Proof with eauto with *.
    intros fs [H H0] x.
    split.
    - destruct H as [f0].
      exists (proj1_sig f0 x).
      apply (in_image f0 (fun f : D ~> D' => proj1_sig f x))...
    - intros y1 H1 y2 H2.
      inversion H1; subst.
      inversion H2; subst.
      rename x0 into f1, x1 into f2.
      destruct (H0 f1 H3 f2 H4) as [f3 [H5 [H6 H7]]].
      exists (proj1_sig f3 x).
      repeat split...
      apply (in_image f3 (fun f : D ~> D' => proj1_sig f x))...
  Qed.

  Lemma sup_of_set_of_squigs_exists_if_it_is_directed {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    let f : D -> D' := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x)) in
    isContinuousMap f.
  Proof with eauto with *.
    intros F F_isDirected f.
    assert (claim1 : isMonotonicMap f).
    { intros x1 x2 H.
      unfold f.
      destruct (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x1) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x1)) as [sup_F1_x H0].
      destruct (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x2) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x2)) as [sup_F2_x H1].
      simpl.
      apply H0.
      intros x' H2.
      inversion H2; subst.
      rename x into f_i.
      transitivity (proj1_sig f_i x2).
      - apply (ContinuousMapOnCpos_isMonotonic)...
        membership.
      - apply H1...
        apply (in_image f_i (fun f_i' : D ~> D' => proj1_sig f_i' x2))...
    }
    apply (the_main_reason_for_introducing_ScottTopology (exist isMonotonicMap f claim1)).
    unfold characterization_of_ContinuousMap_on_cpos.
    simpl.
    intros X H.
    set (Y := image f X).
    destruct (square_up_exists X H) as [sup_X H0].
    assert ( claim2 :
      forall f_i : D ~> D',
      member f_i F ->
      isSupremum (proj1_sig f_i sup_X) (image (fun x : D => proj1_sig f_i x) X)
    ).
    { intros f_i H1.
      assert (H2 : isContinuousMap (proj1_sig f_i)) by membership.
      assert (H3 : characterization_of_ContinuousMap_on_cpos (proj1_sig f_i)) by apply (the_main_reason_for_introducing_ScottTopology (squig_isMonotonic f_i)), (proj2_sig f_i).
      destruct (H3 X H) as [sup_X' [sup_Y' [H4 [H5 H6]]]].
      assert (H7 : sup_X' == sup_X) by now apply (isSupremum_unique X).
      assert (H8 : proj1_sig f_i sup_X' == proj1_sig f_i sup_X) by apply (MonotonicMap_preservesSetoid (proj1_sig f_i) (proj2_sig (squig_isMonotonic f_i)) sup_X' sup_X H7).
      apply (proj2 (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X) _ H5 (proj1_sig f_i sup_X))).
      transitivity (proj1_sig f_i sup_X')...
    }
    assert (claim3 : isSupremum (f sup_X) (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected sup_X))).
    assert (claim4 : isSupremum (f sup_X) (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) F))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs.
      - intros ys H1.
        inversion H1; subst.
        rename x into f_i.
        exists (proj1_sig f_i sup_X)...
      - intros y.
        split.
        + intros H1 y' [ys [H2 H3]].
          inversion H2; subst.
          rename x into f_i.
          assert (H5 := claim2 f_i H4).
          assert (H6 : y' == proj1_sig f_i sup_X) by now apply (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X)).
          assert (H7 : member (proj1_sig f_i sup_X) (image (fun f_i0 : D ~> D' => proj1_sig f_i0 sup_X) F)) by now apply (in_image f_i (fun f_i0 : D ~> D' => proj1_sig f_i0 sup_X)).
          assert (H8 : proj1_sig f_i sup_X =< y)...
        + intros H1.
          apply claim3.
          intros y' H2.
          inversion H2; subst.
          rename x into f_i.
          apply H1.
          exists (image (fun x : D => proj1_sig f_i x) X).
          split...
          apply (in_image f_i (fun f_i0 : D ~> D' => image (fun x : D => proj1_sig f_i0 x) X))...
    }
    assert (claim5 : isSupremum (f sup_X) (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X))).
    { enough (H2 : forall x' : D', member x' (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) F)) <-> member x' (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X))) by now apply (proj2 (isSupremum_ext _ _ H2 _ claim4 _) (Setoid_refl (f sup_X))).
      intros y.
      split.
      - intros H1.
        inversion H1; subst.
        rename X0 into ys.
        inversion H3; subst.
        rename x into f_i.
        inversion H2; subst.
        apply (in_unions (proj1_sig f_i x) (image (fun f_i' : D ~> D' => proj1_sig f_i' x) F)).
        + apply (in_image f_i (fun f_i' : D ~> D' => proj1_sig f_i' x))...
        + apply (in_image x (fun x0 : D => image (fun f_i0 : D ~> D' => proj1_sig f_i0 x0) F))...
      - intros H1.
        inversion H1; subst.
        rename X0 into ys.
        inversion H3; subst.
        inversion H2; subst.
        rename x0 into f_i.
        apply (in_unions (proj1_sig f_i x) (image (fun x' : D => proj1_sig f_i x') X)).
        + apply (in_image x (fun x' : D => proj1_sig f_i x'))...
        + apply (in_image f_i (fun f_i0 : D ~> D' => image (fun x0 : D => proj1_sig f_i0 x0) X))...
    }
    assert (claim6 : isSupremum (f sup_X) (image_sup (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
      intros ys H1.
      inversion H1; subst.
      exists (f x).
      intros y.
      split.
      - intros H3 y' H4.
        inversion H4; subst.
        rename x0 into f_i.
        apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x)))...
      - intros H3.
        assert (H5 : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x))).
        apply H5...
    }
    assert (claim7 : isSupremum (f sup_X) (image f X)).
    { intros y.
      split.
      - intros H1 y' H2.
        inversion H2; subst.
        apply claim6...
        exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F).
        split.
        + apply (in_image x (fun x0 : D => image (fun f_i : D ~> D' => proj1_sig f_i x0) F))...
        + apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x))).
      - intros H1.
        apply claim6.
        intros y' [ys [H2 H3]].
        inversion H2; subst.
        assert (H5 : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x))).
        assert (H6 : y' == f x) by now apply (isSupremum_unique (image (fun f_i : D ~> D' => proj1_sig f_i x) F)).
        transitivity (f x)...
    }
    exists sup_X, (f sup_X)...
  Qed.

  Definition sup_of_set_of_squigs {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : forall F : ensemble (D ~> D'), isDirected F -> (D ~> D') :=
    fun F : ensemble (D ~> D') =>
    fun F_isDirected : isDirected F =>
    exist isContinuousMap (fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x))) (sup_of_set_of_squigs_exists_if_it_is_directed F F_isDirected)
  .

  Lemma sup_of_set_of_squigs_isSupremum {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    isSupremum (sup_of_set_of_squigs F F_isDirected) F.
  Proof with eauto with *.
    intros F F_isDirected f.
    split.
    - intros H f' H0.
      assert (claim1 : forall x : D, proj1_sig f' x =< proj1_sig (sup_of_set_of_squigs F F_isDirected) x).
      { intros x.
        unfold sup_of_set_of_squigs.
        simpl.
        destruct (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x)) as [sup_F_x H1].
        simpl.
        apply H1...
        apply (in_image f' (fun f_i : D ~> D' => proj1_sig f_i x))...
      }
      transitivity (sup_of_set_of_squigs F F_isDirected)...
    - intros H x.
      unfold sup_of_set_of_squigs.
      simpl.
      destruct (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x)) as [sup_F_x H0].
      simpl.
      apply H0.
      intros f' H1.
      inversion H1; subst.
      rename x0 into f_i.
      apply H...
  Qed.

  Lemma bot_of_squigs_isContinuous {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    isContinuousMap (fun _ : D => proj1_sig bottom_exists).
  Proof with eauto with *.
    intros Y [H H0].
    split.
    - intros x1 x2 H1 H2.
      inversion H1; subst.
      apply (in_preimage x2 (fun _ : D => proj1_sig bottom_exists))...
    - intros X [[x_0 H1] H2] sup_X H3 H4.
      inversion H4; subst.
      exists x_0...
  Qed.

  Definition bot_of_squigs {D : Type} {D' : Type} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : D ~> D' :=
    exist isContinuousMap (fun _ : D => proj1_sig (@bottom_exists D' D'_isPoset D'_isCompletePartialOrder)) bot_of_squigs_isContinuous
  .

  Lemma bot_of_squigs_isBottom {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall f : D ~> D',
    bot_of_squigs =< f.
  Proof with eauto with *.
    unfold bot_of_squigs.
    intros f x.
    simpl.
    destruct bottom_exists as [bot_D' H]...
  Qed.

  Local Instance squig_isCompletePartialOrder {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) (D'_requiresCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset) : @isCompletePartialOrder (D ~> D') (@SubPoset (D -> D') isContinuousMap (arrow_isPoset D'_isPoset)) :=
    { bottom_exists :=
      exist _ bot_of_squigs bot_of_squigs_isBottom
    ; square_up_exists :=
      fun F : ensemble (D ~> D') =>
      fun F_isDirected : isDirected F =>
      exist _ (sup_of_set_of_squigs F F_isDirected) (sup_of_set_of_squigs_isSupremum F F_isDirected)
    }
  .

  Lemma seperately_monotonic_iff {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} :
    forall f : (D1 * D2) -> D3,
    ((forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2))) /\ (forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2)))) <-> isMonotonicMap f.
  Proof with eauto with *.
    intros f.
    split.
    - intros [H H0] [x1_1 x2_1] [x1_2 x2_2] [H1 H2].
      simpl in *.
      transitivity (f (x1_1, x2_2)).
      + apply H...
      + apply H0...
    - intros H.
      split.
      + intros x1 x2_1 x2_2 H0.
        apply H.
        simpl...
      + intros x2 x1_1 x1_2 H0.
        apply H.
        simpl...
  Qed.

  Lemma separately_continuous_iff {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isCompletePartialOrder : isCompletePartialOrder D1} `{D2_isCompletePartialOrder : isCompletePartialOrder D2} `{D3_isCompletePartialOrder : isCompletePartialOrder D3} :
    forall f : (D1 * D2) >=> D3,
    ((forall x1 : D1, isContinuousMap (fun x2 : D2 => proj1_sig f (x1, x2))) /\ (forall x2 : D2, isContinuousMap (fun x1 : D1 => proj1_sig f (x1, x2)))) <-> isContinuousMap (proj1_sig f).
  Proof with eauto with *.
    intros f.
    split.
    - intros [H H0].
      apply the_main_reason_for_introducing_ScottTopology.
      intros X H1 Y.
      destruct (square_up_exists X H1) as [[sup_X1 sup_X2] H2].
      set (X1 := image fst X).
      set (X2 := image snd X).
      assert (claim1 : isDirected X1).
      { destruct H1 as [[[x1_0 x2_0] H1] H3].
        split.
        - exists x1_0.
          apply (in_image (x1_0, x2_0) fst)...
        - intros x1_1 H4 x1_2 H5.
          inversion H4; subst.
          inversion H5; subst.
          destruct x as [x1_1 x2_1].
          destruct x0 as [x1_2 x2_2].
          destruct (H3 (x1_1, x2_1) H6 (x1_2, x2_2) H7) as [[x3_1 x3_2] [H8 [[H9 H10] [H11 H12]]]].
          assert (H13 : member x3_1 X1) by now apply (in_image (x3_1, x3_2) fst)...
      }
      assert (claim2 : isDirected X2).
      { destruct H1 as [[[x1_0 x2_0] H1] H3].
        split.
        - exists x2_0.
          apply (in_image (x1_0, x2_0) snd)...
        - intros x2_1 H4 x2_2 H5.
          inversion H4; subst.
          inversion H5; subst.
          destruct x as [x1_1 x2_1].
          destruct x0 as [x1_2 x2_2].
          destruct (H3 (x1_1, x2_1) H6 (x1_2, x2_2) H7) as [[x3_1 x3_2] [H8 [[H9 H10] [H11 H12]]]].
          assert (H13 : member x3_2 X2) by now apply (in_image (x3_1, x3_2) snd)...
      }
      assert ( claim3 :
        forall x1 : D1,
        exists sup_X2_x1 : D2, exists sup_f_X2_x1 : D3, isSupremum sup_X2_x1 X2 /\ isSupremum sup_f_X2_x1 (image (fun x2 : D2 => proj1_sig f (x1, x2)) X2) /\ proj1_sig f (x1, sup_X2_x1) == sup_f_X2_x1
      ).
      { intros x1.
        assert (H3 := the_main_reason_for_introducing_ScottTopology (squig_isMonotonic (exist _ (fun x2 : D2 => proj1_sig f (x1, x2)) (H x1)))).
        unfold squig_isMonotonic in H3.
        simpl in H3.
        apply H3...
      }
      assert ( claim4 :
        forall x2 : D2,
        exists sup_X1_x2 : D1, exists sup_f_X1_x2 : D3, isSupremum sup_X1_x2 X1 /\ isSupremum sup_f_X1_x2 (image (fun x1 : D1 => proj1_sig f (x1, x2)) X1) /\ proj1_sig f (sup_X1_x2, x2) == sup_f_X1_x2
      ).
      { intros x2.
        assert (H3 := the_main_reason_for_introducing_ScottTopology (squig_isMonotonic (exist _ (fun x1 : D1 => proj1_sig f (x1, x2)) (H0 x2)))).
        unfold squig_isMonotonic in H3.
        simpl in H3.
        apply H3...
      }
      assert (XXX : isSupremum sup_X1 X1 /\ isSupremum sup_X2 X2).
      { destruct (square_up_exists X1 claim1) as [sup_X1' H3].
        destruct (square_up_exists X2 claim2) as [sup_X2' H4].
        assert (H5 : isSupremum (sup_X1', sup_X2') X).
        { intros [x1 x2].
          split.
          - intros [H5 H6] [x1' x2'] H7.
            simpl in *.
            split.
            + apply H3...
              apply (in_image (x1', x2') fst)...
            + apply H4...
              apply (in_image (x1', x2') snd)...
          - intros H5.
            split.
            + apply H3.
              intros x1' H6.
              inversion H6; subst.
              destruct x as [x1' x2'].
              apply (proj1 (H5 (x1', x2') H7)).
            + apply H4.
              intros x2' H6.
              inversion H6; subst.
              destruct x as [x1' x2'].
              apply (proj2 (H5 (x1', x2') H7)).
        }
        assert (H6 : (sup_X1, sup_X2) == (sup_X1', sup_X2')) by now apply (isSupremum_unique X).
        destruct H6 as [H6 H7].
        simpl in *.
        split.
        - symmetry in H6.
          apply (proj2 (isSupremum_unique X1 sup_X1' H3 sup_X1) H6).
        - symmetry in H7.
          apply (proj2 (isSupremum_unique X2 sup_X2' H4 sup_X2) H7).
      }
      destruct XXX as [claim5 claim6].
      assert (claim7 : isSupremum (proj1_sig f (sup_X1, sup_X2)) (image (fun x2 : D2 => proj1_sig f (sup_X1, x2)) X2)).
      { destruct (claim3 sup_X1) as [sup_X2_x1 [sup_f_X1_x2 [H3 [H4 H5]]]].
        assert (H6 : isSupremum (proj1_sig f (sup_X1, sup_X2)) (image (fun x2 : D2 => proj1_sig f (sup_X1, x2)) X2) <-> sup_f_X1_x2 == proj1_sig f (sup_X1, sup_X2)) by now apply (isSupremum_unique (image (fun x2 : D2 => proj1_sig f (sup_X1, x2)) X2)).
        apply H6.
        transitivity (proj1_sig f (sup_X1, sup_X2_x1)).
        - symmetry...
        - apply MonotonicMap_preservesSetoid.
          + membership.
          + split.
            * apply Setoid_refl.
            * apply (isSupremum_unique X2)...
      }
      assert ( claim8 :
        forall x2 : D2,
        member x2 X2 ->
        isSupremum (proj1_sig f (sup_X1, x2)) (image (fun x1 : D1 => proj1_sig f (x1, x2)) X1)
      ).
      { intros x2 H3.
        destruct (claim4 x2) as [sup_X1' [sup_f_X1_x2' [H4 [H5 H6]]]].
        assert (H7 : isSupremum (proj1_sig f (sup_X1, x2)) (image (fun x1 : D1 => proj1_sig f (x1, x2)) X1) <-> sup_f_X1_x2' == proj1_sig f (sup_X1, x2)) by now apply (isSupremum_unique (image (fun x1 : D1 => proj1_sig f (x1, x2)) X1)).
        apply H7.
        transitivity (proj1_sig f (sup_X1', x2)).
        - symmetry...
        - apply MonotonicMap_preservesSetoid.
          + membership.
          + split.
            * apply (isSupremum_unique X1)...
            * apply Setoid_refl.
      }
      assert (claim9 : isSupremum (proj1_sig f (sup_X1, sup_X2)) (image_sup (image (fun x2 : D2 => image (fun x1 : D1 => proj1_sig f (x1, x2)) X1) X2))).
      { intros y.
        split.
        - intros H3 y' [ys [H4 H5]].
          inversion H4; subst.
          rename x into x2.
          assert (H7 : isSupremum (proj1_sig f (sup_X1, x2)) (image (fun x1 : D1 => proj1_sig f (x1, x2)) X1)) by now apply claim8.
          assert (H8 : y' == proj1_sig f (sup_X1, x2)) by now apply (isSupremum_unique (image (fun x1 : D1 => proj1_sig f (x1, x2)) X1)).
          assert (H9 : proj1_sig f (sup_X1, x2) =< proj1_sig f (sup_X1, sup_X2)) by now apply (ContinuousMapOnCpos_isMonotonic (fun x2' : D2 => proj1_sig f (sup_X1, x2')) (H sup_X1)), claim6...
        - intros H7.
          apply claim7.
          intros y' H8.
          inversion H8; subst.
          rename x into x2.
          apply H7...
          exists (image (fun x1 : D1 => proj1_sig f (x1, x2)) X1).
          split.
          + apply (in_image _ (fun x0 : D2 => image (fun x1 : D1 => proj1_sig f (x1, x0)) X1))...
          + apply claim8...
      }
      assert (claim10 : isSupremum (proj1_sig f (sup_X1, sup_X2)) (unions (image (fun x2 : D2 => image (fun x1 : D1 => proj1_sig f (x1, x2)) X1) X2))).
      { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
        intros ys H3.
        inversion H3; subst.
        rename x into x2.
        exists (proj1_sig f (sup_X1, x2))...
      }
      assert (claim11 : isSupremum (proj1_sig f (sup_X1, sup_X2)) (image (proj1_sig f) X)).
      { intros y.
        split.
        - intros H3 y' H4.
          inversion H4; subst.
          apply claim10.
          + apply H3.
          + destruct x as [x1 x2].
            apply (in_unions _ (image (fun x1' : D1 => proj1_sig f (x1', x2)) X1)).
            * apply (in_image _ (fun x1' : D1 => proj1_sig f (x1', x2))), (in_image (x1, x2) fst)...
            * apply (in_image _ (fun x0 : D2 => image (fun x3 : D1 => proj1_sig f (x3, x0)) X1)), (in_image (x1, x2) snd)...
        - intros H3.
          apply claim10.
          intros y' H4.
          inversion H4; subst.
          rename X0 into ys.
          inversion H6; subst.
          rename x into x2_2.
          inversion H5; subst.
          rename x into x1_1.
          inversion H8; subst.
          destruct x as [x1_1 x2_1].
          inversion H7; subst.
          destruct x as [x1_2 x2_2].
          destruct H1 as [H1 H11].
          destruct (H11 (x1_1, x2_1) H9 (x1_2, x2_2) H10) as [[x3_1 x3_2] [H12 [[H13 H14] [H15 H16]]]].
          simpl in *.
          assert (claim11_aux1 : proj1_sig f (x1_1, x2_2) =< proj1_sig f (x3_1, x3_2)).
          { transitivity (proj1_sig f (x1_1, x3_2)).
            - apply (ContinuousMapOnCpos_isMonotonic (fun x2 : D2 => proj1_sig f (x1_1, x2)))...
            - apply (ContinuousMapOnCpos_isMonotonic (fun x1 : D1 => proj1_sig f (x1, x3_2)))...
          }
          transitivity (proj1_sig f (x3_1, x3_2))...
      }
      exists (sup_X1, sup_X2), (proj1_sig f (sup_X1, sup_X2))...
    - intros H.
      assert (XXX1 : forall x1 : D1, isMonotonicMap (fun x2 : D2 => proj1_sig f (x1, x2))).
      { intros x1 x2_1 x2_2 H1.
        apply (proj2_sig f).
        split... 
      }
      assert (XXX2 : forall x2 : D2, isMonotonicMap (fun x1 : D1 => proj1_sig f (x1, x2))).
      { intros x2 x1_1 x1_2 H1.
        apply (proj2_sig f).
        split... 
      }
      split.
      + intros x1.
        apply (the_main_reason_for_introducing_ScottTopology (exist _ (fun x2 : D2 => proj1_sig f (x1, x2)) (XXX1 x1))).
        intros X2 H0 Y.
        destruct (square_up_exists X2 H0) as [sup_X2 H1].
        set (X := image (fun x2 : D2 => (x1, x2)) X2).
        assert (claim1 : isDirected X).
        { destruct H0 as [[x2_0 H0] H2].
          split.
          - exists (x1, x2_0).
            apply (in_image _ (fun x2 : D2 => (x1, x2)))...
          - intros [x1_1 x2_1] H3 [x1_2 x2_2] H4.
            inversion H3; subst x1_1; subst.
            inversion H4; subst x1_2; subst.
            rename H8 into H5, H9 into H6.
            destruct (H2 x2_1 H5 x2_2 H6) as [x3_2 [H7 [H8 H9]]].
            exists (x1, x3_2).
            repeat split...
        }
        destruct (square_up_exists X claim1) as [sup_X H2].
        assert (claim2 : (x1, sup_X2) == sup_X).
        { apply (isSupremum_unique X)...
          intros [x_1 x_2].
          split.
          - intros [H3 H4] [x_1' x_2'] H5.
            inversion H5; subst x_1'; subst.
            simpl.
            split...
          - intros H3.
            simpl.
            split.
            + destruct H0 as [[x2_0 H0] H4].
              apply (H3 (x1, x2_0))...
            + apply H1.
              intros x_2' H4.
              apply (H3 (x1, x_2'))...
        }
        assert (claim3 : proj1_sig f (x1, sup_X2) == proj1_sig f sup_X).
        { apply MonotonicMap_preservesSetoid.
          - membership.
          - apply claim2.
        }
        assert (XXX : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image (proj1_sig f) X) /\ proj1_sig f sup_X' == sup_Y') by now apply the_main_reason_for_introducing_ScottTopology.
        destruct XXX as [sup_X' [sup_Y' [H3 [H4 H5]]]].
        assert (claim4 : isSupremum (proj1_sig f sup_X) (image (proj1_sig f) X) <-> sup_Y' == proj1_sig f sup_X) by now apply (isSupremum_unique (image (proj1_sig f) X)).
        assert (claim5 : isSupremum (proj1_sig f sup_X) (image (proj1_sig f) X)).
        { apply claim4.
          transitivity (proj1_sig f sup_X').
          - symmetry...
          - assert (H6 : sup_X' == sup_X) by now apply (isSupremum_unique X).
            apply MonotonicMap_preservesSetoid.
            + membership.
            + apply H6.
        }
        assert (claim6 : forall y : D3, member y (image (proj1_sig f) X) <-> member y Y).
        { intros y.
          split.
          - intros H6.
            inversion H6; subst.
            inversion H7; subst.
            rename x0 into x2.
            apply (in_image _ (fun x2 : D2 => proj1_sig f (x1, x2)))...
          - intros H6.
            inversion H6; subst.
            rename x into x2.
            apply (in_image _ (proj1_sig f))...
        }
        assert (claim7 : isSupremum (proj1_sig f sup_X) Y) by apply (proj2 (isSupremum_ext _ _ claim6 _ claim5 _) (Setoid_refl _)).
        exists sup_X2, (proj1_sig f sup_X)...
      + intros x2.
        apply (the_main_reason_for_introducing_ScottTopology (exist _ (fun x1 : D1 => proj1_sig f (x1, x2)) (XXX2 x2))).
        intros X1 H0 Y.
        destruct (square_up_exists X1 H0) as [sup_X1 H1].
        set (X := image (fun x1 : D1 => (x1, x2)) X1).
        assert (YYY : forall x1 : D1, member x1 X1 -> member (x1, x2) X).
        { intros x1 H2.
          apply (in_image _ (fun x1 : D1 => (x1, x2))), H2.
        }
        assert (claim1 : isDirected X).
        { destruct H0 as [[x1_0 H0] H2].
          split.
          - exists (x1_0, x2).
            apply (in_image _ (fun x1 : D1 => (x1, x2)))...
          - intros [x1_1 x2_1] H3 [x1_2 x2_2] H4.
            inversion H3; subst x2_1; subst.
            inversion H4; subst x2_2; subst.
            rename H8 into H5, H9 into H6.
            destruct (H2 x1_1 H5 x1_2 H6) as [x3_1 [H7 [H8 H9]]].
            exists (x3_1, x2).
            repeat split...
        }
        destruct (square_up_exists X claim1) as [sup_X H2].
        assert (claim2 : (sup_X1, x2) == sup_X).
        { apply (isSupremum_unique X)...
          intros [x_1 x_2].
          split.
          - intros [H3 H4] [x_1' x_2'] H5.
            inversion H5; subst x_1'; subst.
            simpl.
            split...
          - intros H3.
            simpl.
            split.
            + apply H1.
              intros x_1' H4.
              apply (H3 (x_1', x2))...
            + destruct H0 as [[x1_0 H0] H4].
              apply (H3 (x1_0, x2))...
        }
        assert (claim3 : proj1_sig f (sup_X1, x2) == proj1_sig f sup_X).
        { apply MonotonicMap_preservesSetoid.
          - membership.
          - apply claim2.
        }
        assert (XXX : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image (proj1_sig f) X) /\ proj1_sig f sup_X' == sup_Y') by now apply the_main_reason_for_introducing_ScottTopology.
        destruct XXX as [sup_X' [sup_Y' [H3 [H4 H5]]]].
        assert (claim4 : isSupremum (proj1_sig f sup_X) (image (proj1_sig f) X) <-> sup_Y' == proj1_sig f sup_X) by now apply (isSupremum_unique (image (proj1_sig f) X)).
        assert (claim5 : isSupremum (proj1_sig f sup_X) (image (proj1_sig f) X)).
        { apply claim4.
          transitivity (proj1_sig f sup_X').
          - symmetry...
          - assert (H6 : sup_X' == sup_X) by now apply (isSupremum_unique X).
            apply MonotonicMap_preservesSetoid.
            + membership.
            + apply H6.
        }
        assert (claim6 : forall y : D3, member y (image (proj1_sig f) X) <-> member y Y).
        { intros y.
          split.
          - intros H6.
            inversion H6; subst.
            inversion H7; subst.
            rename x0 into x1.
            apply (in_image _ (fun x1 : D1 => proj1_sig f (x1, x2)))...
          - intros H6.
            inversion H6; subst.
            rename x into x1.
            apply (in_image _ (proj1_sig f))...
        }
        assert (claim7 : isSupremum (proj1_sig f sup_X) Y) by apply (proj2 (isSupremum_ext _ _ claim6 _ claim5 _) (Setoid_refl _)).
        exists sup_X1, (proj1_sig f sup_X)...
  Qed.

  Lemma ScottApp_isMontonic {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    isMonotonicMap (@uncurry (D ~> D') D D' (@proj1_sig (D -> D') isContinuousMap)).
  Proof with eauto with *.
    intros [f1 x1] [f2 x2] [H H0].
    simpl in *.
    assert (H1 : isContinuousMap (proj1_sig f1)) by membership.
    transitivity (proj1_sig f1 x2); [apply ContinuousMapOnCpos_isMonotonic | apply H]...
  Qed.

  Definition ScottApp {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) (D'_requiresCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset) : ((D ~> D') * D) >=> D' :=
    exist _ (@uncurry (D ~> D') D D' (@proj1_sig (D -> D') isContinuousMap)) ScottApp_isMontonic
  .

  Lemma ScottApp_isContinuous {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    isContinuousMap (proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder)).
  Proof with eauto with *.
    apply separately_continuous_iff.
    split.
    - unfold ScottApp.
      simpl.
      intros f.
      membership.
    - intros x.
      assert (XXX : isMonotonicMap (fun f : D ~> D' => proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (f, x))).
      { intros f1 f2 H.
        unfold ScottApp...
      }
      apply (the_main_reason_for_introducing_ScottTopology (exist isMonotonicMap (fun f : D ~> D' => proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (f, x)) XXX)).
      intros fs fs_isDirected Y.
      set (f := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_set_of_squigs_is_well_defined fs fs_isDirected x))).
      set (sup_fs := exist _ f (sup_of_set_of_squigs_exists_if_it_is_directed fs fs_isDirected)).
      assert (claim1 : forall x : D, isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (fun x : D => proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_set_of_squigs_is_well_defined fs fs_isDirected x))).
      assert (claim2 : isSupremum sup_fs fs).
      { intros g.
        simpl.
        split.
        - intros H g' H0 x'.
          apply (claim1 x')...
          apply (in_image _ (fun f_i : D ~> D' => proj1_sig f_i x'))...  
        - intros H x'.
          apply (claim1 x').
          intros g' H0.
          inversion H0; subst.
          rename x0 into g'.
          apply (H g')...
      }
      assert (claim3 : isSupremum (proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (sup_fs, x)) Y).
      { intros y.
        split.
        - intros H y' H0.
          apply (claim1 x)...
        - intros H.
          apply (claim1 x)...
      }
      exists sup_fs, (proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (sup_fs, x))...
  Qed.

End ClassicalCpoTheory.
