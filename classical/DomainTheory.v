Require Import Coq.Lists.List.
Require Import DschingisKhan.classical.ExclusiveMiddle.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module ClassicalCpoTheory.

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory BasicTopology ConstructiveCpoTheory ExclusiveMiddle.

  Definition U {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D :=
    fun x : D =>
    fun z : D =>
    ~ z =< x
  .

  Global Hint Unfold U : my_hints.

  Lemma U_x_isOpen {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} :
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
    { intros x y z y_in_U_x y_le_z z_in_U_x.
      contradiction y_in_U_x...
    }
    intros x.
    split...
    intros X [nonempty_X X_closed_under_le] sup_X sup_X_isSupremum_of_X sup_X_in_U_x.
    assert (claim2 : ~ (forall x' : D, x' =< x \/ ~ member x' X)).
    { intros every_member_of_X_is_either_less_than_or_equal_to_x.
      contradiction sup_X_in_U_x.
      apply (proj2 (sup_X_isSupremum_of_X x)).
      firstorder.
    }
    destruct (not_all_ex_not D (fun x0 : D => (x0 =< x \/ ~ member x0 X)) claim2) as [x0 x0_is_a_member_of_X_which_is_less_than_or_equal_to_x].
    exists x0.
    apply in_intersection_iff.
    destruct (classic (member x0 X)); tauto.
  Qed.

  Lemma ContinuousMapOnCpos_isMonotonic {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    isContinuousMap f ->
    isMonotonicMap f.
  Proof with eauto with *.
    intros f f_continuous x1 x2 x1_le_x2.
    apply NNPP.
    intros f_x1_le_f_x2_is_false.
    assert (f_x1_in_U_f_x2 : member (f x1) (U (f x2))) by now unfold U.
    assert (x1_in_preimage_f_U_f_x2 : member x1 (preimage f (U (f x2)))) by now constructor.
    assert (preimage_f_U_f_x2_isOpen : isOpen (preimage f (U (f x2)))) by now apply f_continuous, U_x_isOpen.
    assert (x2_in_f_U_f_x2 : member x2 (preimage f (U (f x2)))) by now apply (proj1 preimage_f_U_f_x2_isOpen x1 x2).
    assert (f_x2_in_U_f_x2 : member (f x2) (U (f x2))) by now inversion x2_in_f_U_f_x2...
  Qed.

  Lemma ContinuousMapOnCpos_preservesDirected {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    isDirected (image f X).
  Proof with eauto with *.
    intros f f_continuous X [[x0 x0_in_X] X_closed_under_le].
    assert (f_monotonic : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMapOnCpos_isMonotonic.
    split.
    - exists (f x0)...
    - intros y1 y1_in_image_f_X y2 y2_in_image_f_X.
      rewrite in_image_iff in y1_in_image_f_X, y2_in_image_f_X.
      destruct y1_in_image_f_X as [x1 [Heq1 x1_in_X]].
      destruct y2_in_image_f_X as [x2 [Heq2 x2_in_X]].
      subst y1 y2.
      destruct (X_closed_under_le x1 x1_in_X x2 x2_in_X) as [x3 [x3_in_X [x1_le_x3 x2_le_x3]]].
      exists (f x3).
      repeat split...
  Qed.

  Lemma ContinuousMapOnCpos_preservesSupremum_aux1 {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    forall image_f_X_isDirected : isDirected (image f X),
    f sup_X == proj1_sig (square_up_exists (image f X) image_f_X_isDirected).
  Proof with eauto with *.
    intros f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X image_f_X_isDirected.
    set (Y := image f X).
    assert (f_monotonic : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMapOnCpos_isMonotonic.
    destruct (square_up_exists Y image_f_X_isDirected) as [sup_Y sup_Y_isSupremum_of_Y].
    assert (claim1 : sup_Y =< f sup_X).
    { apply sup_Y_isSupremum_of_Y.
      intros y y_in_Y.
      apply in_image_iff in y_in_Y.
      destruct y_in_Y as [x [Heq x_in_X]].
      subst y...
    }
    assert (claim2 : f sup_X =< sup_Y).
    { apply NNPP.
      intros f_sup_X_le_sup_Y_is_false.
      assert (f_sup_X_in_U_sup_Y : member (f sup_X) (U sup_Y)) by now unfold U.
      assert (sup_X_in_preimage_f_U_sup_Y : member sup_X (preimage f (U sup_Y))) by now constructor.
      assert (f_U_sup_Y_isOpen : isOpen (preimage f (U sup_Y))) by now apply f_continuous, U_x_isOpen.
      destruct ((proj2 f_U_sup_Y_isOpen) X X_isDirected sup_X sup_X_isSupremum_of_X sup_X_in_preimage_f_U_sup_Y) as [x1 x1_in_both_X_and_preimage_f_U_sup_Y].
      apply in_intersection_iff in x1_in_both_X_and_preimage_f_U_sup_Y.
      assert (f_x1_in_image_f_X : member (f x1) (image f X)) by now constructor; apply (proj1 x1_in_both_X_and_preimage_f_U_sup_Y).
      assert (f_x1_in_U_sup_Y : member (f x1) (U sup_Y)) by now apply in_preimage_iff.
      contradiction f_x1_in_U_sup_Y.
      apply sup_Y_isSupremum_of_Y...
    }
    apply Poset_asym...
  Qed.

  Lemma ContinuousMapsOnCpo_preservesSupremum_aux2 {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    forall sup_Y : D',
    isSupremum sup_Y (image f X) <-> f sup_X == sup_Y.
  Proof with eauto with *.
    intros f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X sup_Y.
    assert (image_f_X_isDirected := ContinuousMapOnCpos_preservesDirected f f_continuous X X_isDirected).
    split.
    - assert (claim1 := square_up_isSupremum (image f X) image_f_X_isDirected).
      transitivity (proj1_sig (square_up_exists (image f X) image_f_X_isDirected)).
      + exact (ContinuousMapOnCpos_preservesSupremum_aux1 f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X image_f_X_isDirected).
      + apply (isSupremum_unique (image f X))...
    - intros f_sup_X_eq_sup_Y.
      assert (claim2 := ContinuousMapOnCpos_preservesSupremum_aux1 f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X image_f_X_isDirected).
      assert (claim3 := square_up_isSupremum (image f X) (image_f_X_isDirected)).
      assert (claim4 := proj2 (isSupremum_unique (image f X) (proj1_sig (square_up_exists (image f X) image_f_X_isDirected)) claim3 sup_Y)).
      apply claim4...
  Qed.

  Global Hint Resolve ContinuousMapsOnCpo_preservesSupremum_aux2 : my_hints.

  Definition ContinuousMapsOnCpo_preservesSupremum {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    {sup_Y : D' | isSupremum sup_Y (image f X) /\ f sup_X == sup_Y}.
  Proof.
    intros f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X.
    exists (f sup_X).
    split.
    - apply (proj2 (ContinuousMapsOnCpo_preservesSupremum_aux2 f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X (f sup_X)))...
      reflexivity.
    - reflexivity.
  Defined.

  Definition characterization_of_ContinuousMap_on_cpos {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : (D -> D') -> Prop :=
    fun f : D -> D' =>
    forall X : ensemble D,
    @isDirected D D_isPoset X ->
    exists sup_X : D, exists sup_Y : D', @isSupremum D D_isPoset sup_X X /\ @isSupremum D' D'_isPoset sup_Y (image f X) /\ @eqProp D' (@Poset_requiresSetoid D' D'_isPoset) (f sup_X) sup_Y
  .

  Theorem the_main_reason_for_introducing_ScottTopology {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    (forall x1 : D, forall x2 : D, x1 == x2 -> f x1 == f x2) ->
    isContinuousMap f <-> characterization_of_ContinuousMap_on_cpos f.
  Proof with eauto with *.
    assert (claim1 : forall f : D >=> D', isContinuousMap (proj1_sig f) -> forall x1 : D, forall x2 : D, x1 =< x2 -> proj1_sig f x1 =< proj1_sig f x2) by apply (fun f : D >=> D' => ContinuousMapOnCpos_isMonotonic (proj1_sig f)).
    intros f f_preserves_eq.
    split.
    - intros f_continuous X X_isDirected.
      set (Y := image f X).
      assert (H3 : isDirected Y) by now apply ContinuousMapOnCpos_preservesDirected.
      destruct (square_up_exists X X_isDirected) as [sup_X sup_X_isSupremum_of_X].
      destruct (ContinuousMapsOnCpo_preservesSupremum f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X) as [sup_Y [sup_Y_isSupremum_of_Y f_sup_X_eq_sup_Y]].
      exists sup_X, sup_Y...
    - intros characterstic_properties_of_continuous_map.
      assert (claim2 : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2).
      { intros x1 x2 H.
        set (X := finite [x1; x2]).
        set (Y := image f X).
        assert (claim2_aux1 : isSupremum x2 X).
        { intros x.
          split.
          - intros H0 x' H1.
            apply in_finite_iff in H1.
            destruct H1 as [H1 | [H1 | []]]; subst...
          - intros H0...
        }
        assert (claim2_aux2 : isDirected X).
        { split.
          - exists x1...
          - intros x1' H0 x2' H1.
            exists x2.
            enough (H3 : x1' =< x2 /\ x2' =< x2)...
        }
        destruct (characterstic_properties_of_continuous_map X claim2_aux2) as [sup_X [sup_Y [sup_X_isSupremum_of_X [sup_Y_isSupremum_of_Y f_sup_X_eq_sup_Y]]]].
        assert (sup_X_eq_x2 : sup_X == x2) by now apply (isSupremum_unique X).
        apply f_preserves_eq in sup_X_eq_x2.
        transitivity (sup_Y).
        - apply sup_Y_isSupremum_of_Y...
        - transitivity (f sup_X)...
      }
      intros O O_isOpen.
      split.
      + intros x1 x2 x_in_preimage_f_O x_le_y.
        rewrite in_preimage_iff in x_in_preimage_f_O.
        constructor.
        apply (proj1 O_isOpen (f x1) (f x2))...
      + intros X X_isDirected sup_X sup_X_isSupremum_of_X sup_X_in_preimage_f_O.
        destruct (characterstic_properties_of_continuous_map X X_isDirected) as [sup_X' [sup_Y' [sup_X'_isSupremum_of_X [sup_Y'_isSupremum_of_image_f_X f_sup_X'_eq_sup_Y']]]].
        assert (sup_X_eq_sup_X' : sup_X == sup_X') by now apply (isSupremum_unique X).
        assert (f_sup_X_in_O : member (f sup_X) O) by now apply in_preimage_iff.
        assert (claim3 : isDirected (image f X)).
        { destruct X_isDirected as [[x1_0 x1_0_in_X] X_closed_under_le].
          split.
          - exists (f x1_0)...
          - intros y1 y1_in_image_f_X y2 y2_in_image_f_X.
            apply in_image_iff in y1_in_image_f_X, y2_in_image_f_X.
            destruct y1_in_image_f_X as [x1 [Heq1 x1_in_X]].
            destruct y2_in_image_f_X as [x2 [Heq2 x2_in_X]].
            subst y1 y2.
            destruct (X_closed_under_le x1 x1_in_X x2 x2_in_X) as [x3 [x3_in_X [x1_le_x3 x2_le_x3]]].
            exists (f x3).
            repeat split...
        }
        assert (claim4 : sup_Y' == f sup_X).
        { transitivity (f sup_X').
          - symmetry...
          - apply f_preserves_eq...
        }
        assert (claim5 : nonempty (intersection (image f X) O)).
        { apply (proj2 O_isOpen (image f X) claim3 (f sup_X))...
          apply (isSupremum_unique (image f X) sup_Y' sup_Y'_isSupremum_of_image_f_X)...
        }
        destruct claim5 as [y y_in_image_f_X_and_O].
        apply in_intersection_iff in y_in_image_f_X_and_O.
        destruct y_in_image_f_X_and_O as [y_in_image_f_X y_in_O].
        apply in_image_iff in y_in_image_f_X.
        destruct y_in_image_f_X as [x [y_eq_f_x x_in_X]].
        subst y...
  Qed.

  Local Instance ContinuousMap_isPoset {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) (D'_requiresCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset) : isPoset (@sig (D -> D') (@isContinuousMap D D' (ScottTopology D_requiresCompletePartialOrder) (ScottTopology D'_requiresCompletePartialOrder))) :=
    @SubPoset (D -> D') (@isContinuousMap D D' (ScottTopology D_requiresCompletePartialOrder) (ScottTopology D'_requiresCompletePartialOrder)) (arrow_isPoset D'_isPoset)
  .

  Definition squig_isMonotonic {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} : (D ~> D') -> (D >=> D') :=
    fun f : D ~> D' =>
    exist isMonotonicMap (proj1_sig f) (ContinuousMapOnCpos_isMonotonic (proj1_sig f) (proj2_sig f))
  .

(*

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

*)

End ClassicalCpoTheory.
