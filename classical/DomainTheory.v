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
      apply in_image_iff in y1_in_image_f_X, y2_in_image_f_X.
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

  Lemma prove_monotonicity {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    (forall x1 : D, forall x2 : D, x1 == x2 -> f x1 == f x2) ->
    characterization_of_ContinuousMap_on_cpos f ->
    forall x1 : D,
    forall x2 : D,
    x1 =< x2 ->
    f x1 =< f x2.
  Proof with eauto with *.
    intros f f_preserves_eq f_property x1 x2 x1_le_x2.
    set (X := finite [x1; x2]).
    set (Y := image f X).
    assert (claim1 : isSupremum x2 X).
    { intros x.
      split.
      - intros x2_le_x x0 x0_in_X.
        apply in_finite_iff in x0_in_X.
        destruct x0_in_X as [x1_eq_x0 | [x2_eq_x0 | []]]; subst...
      - intros x_is_an_upper_bound_of_X...
    }
    assert (claim2 : isDirected X).
    { split.
      - exists x1...
      - intros x1' x1'_in_X x2' x2'_in_X.
        exists x2.
        enough (so_we_obtain : x1' =< x2 /\ x2' =< x2)...
    }
    destruct (f_property X claim2) as [sup_X [sup_Y [sup_X_isSupremum_of_X [sup_Y_isSupremum_of_Y f_sup_X_eq_sup_Y]]]].
    assert (sup_X_eq_x2 : sup_X == x2) by now apply (isSupremum_unique X).
    apply f_preserves_eq in sup_X_eq_x2.
    transitivity (sup_Y)...
  Qed.

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
    - intros f_property.
      assert (claim2 := prove_monotonicity f f_preserves_eq f_property).
      intros O O_isOpen.
      split.
      + intros x1 x2 x_in_preimage_f_O x_le_y.
        apply (in_preimage_iff x1) in x_in_preimage_f_O.
        constructor.
        apply (proj1 O_isOpen (f x1) (f x2))...
      + intros X X_isDirected sup_X sup_X_isSupremum_of_X sup_X_in_preimage_f_O.
        destruct (f_property X X_isDirected) as [sup_X' [sup_Y' [sup_X'_isSupremum_of_X [sup_Y'_isSupremum_of_image_f_X f_sup_X'_eq_sup_Y']]]].
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

  Definition squig_isMonotonic {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : (D ~> D') -> (D >=> D') :=
    fun f : D ~> D' =>
    exist isMonotonicMap (proj1_sig f) (ContinuousMapOnCpos_isMonotonic (proj1_sig f) (proj2_sig f))
  .

  Lemma sup_of_set_of_squigs_is_well_defined {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    isDirected F ->
    forall x : D,
    isDirected (image (fun f_i : D ~> D' => proj1_sig f_i x) F).
  Proof with eauto with *.
    intros F [nonempty_F F_closed_under_le] x.
    split.
    - destruct nonempty_F as [f0].
      exists (proj1_sig f0 x).
      apply in_image_iff...
    - intros y1 y1_in y2 y2_in.
      apply in_image_iff in y1_in, y2_in.
      destruct y1_in as [f1 [y1_is f1_in]].
      destruct y2_in as [f2 [y2_is f2_in]].
      subst y1 y2.
      destruct (F_closed_under_le f1 f1_in f2 f2_in) as [f3 [f3_in [f1_le_f3 f2_le_f3]]].
      exists (proj1_sig f3 x).
      repeat split...
  Qed.

  Lemma sup_of_set_of_squigs_exists_if_it_is_directed {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    let f : D -> D' := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x)) in
    isContinuousMap f.
  Proof with eauto with *.
    intros F F_isDirected f.
    assert (claim1 : isMonotonicMap f).
    { intros x1 x2 H.
      assert (claim1_aux1 := square_up_isSupremum (image (fun f_i : D ~> D' => proj1_sig f_i x1) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x1)).
      assert (claim1_aux2 := square_up_isSupremum (image (fun f_i : D ~> D' => proj1_sig f_i x2) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x2)).
      apply claim1_aux1.
      intros y y_in.
      apply in_image_iff in y_in.
      destruct y_in as [f_i [y1_is f_i_in]].
      subst y.
      transitivity (proj1_sig f_i x2).
      - apply (ContinuousMapOnCpos_isMonotonic)...
        membership.
      - apply claim1_aux2...
    }
    apply (the_main_reason_for_introducing_ScottTopology f (MonotonicMap_preservesSetoid f claim1)).
    intros X X_isDirected.
    set (Y := image f X).
    destruct (square_up_exists X X_isDirected) as [sup_X sup_X_isSupremum_of_X].
    assert ( claim2 :
      forall f_i : D ~> D',
      member f_i F ->
      isSupremum (proj1_sig f_i sup_X) (image (fun x : D => proj1_sig f_i x) X)
    ).
    { intros f_i f_i_in.
      assert (f_i_continuous : isContinuousMap (proj1_sig f_i)) by membership.
      assert (f_i_preserves_eq := MonotonicMap_preservesSetoid (proj1_sig f_i) (ContinuousMapOnCpos_isMonotonic (proj1_sig f_i) f_i_continuous)).
      assert (f_i_property : characterization_of_ContinuousMap_on_cpos (proj1_sig f_i)) by apply (the_main_reason_for_introducing_ScottTopology (proj1_sig (squig_isMonotonic f_i)) f_i_preserves_eq), (proj2_sig f_i).
      destruct (f_i_property X X_isDirected) as [sup_X' [sup_Y' [sup_X'_isSupremum_of_X [sup_Y'_isSupremum_of_image_f_i_X f_i_sup_X'_eq_sup_Y']]]].
      assert (sup_X'_eq_sup_X : sup_X' == sup_X) by now apply (isSupremum_unique X).
      assert (f_i_sup_X_eq_f_i_sup_X' : proj1_sig f_i sup_X' == proj1_sig f_i sup_X) by now apply f_i_preserves_eq.
      apply (proj2 (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X) sup_Y' sup_Y'_isSupremum_of_image_f_i_X (proj1_sig f_i sup_X)))...
    }
    assert (claim3 : isSupremum (f sup_X) (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected sup_X))).
    assert (claim4 : isSupremum (f sup_X) (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) F))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs.
      - intros ys ys_in.
        apply in_image_iff in ys_in.
        destruct ys_in as [f_i [ys_is f_i_in]].
        subst ys...
      - intros y.
        split.
        + intros f_sup_X_le_y y' [ys [ys_in y'_isSupremum_of_ys]].
          apply in_image_iff in ys_in.
          destruct ys_in as [f_i [ys_is f_i_in]].
          subst ys.
          assert (f_i_sup_X_isSupremum := claim2 f_i f_i_in).
          assert (y'_eq : y' == proj1_sig f_i sup_X) by now apply (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X)).
          assert (f_i_sup_X_in : member (proj1_sig f_i sup_X) (image (fun f_i0 : D ~> D' => proj1_sig f_i0 sup_X) F))...
        + intros y_is_an_upper_bound.
          apply claim3.
          intros y' y'_in.
          apply in_image_iff in y'_in.
          destruct y'_in as [f_i [y'_is f_i_in]].
          subst y'.
          apply y_is_an_upper_bound.
          exists (image (fun x : D => proj1_sig f_i x) X).
          split...
    }
    assert (claim5 : isSupremum (f sup_X) (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X))).
    { enough (claim5_aux1 : forall x' : D', member x' (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) F)) <-> member x' (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X))) by now apply (proj2 (isSupremum_ext _ _ claim5_aux1 _ claim4 _) (Setoid_refl (f sup_X))).
      intros y.
      split.
      - intros y_in.
        apply in_unions_iff in y_in.
        destruct y_in as [ys [y_in ys_in]].
        apply in_image_iff in ys_in.
        destruct ys_in as [f_i [ys_is f_i_in]].
        subst ys.
        apply in_image_iff in y_in.
        destruct y_in as [x [y_is x_in]].
        subst y.
        exists (image (fun f_i' : D ~> D' => proj1_sig f_i' x) F)...
      - intros y_in.
        apply in_unions_iff in y_in.
        destruct y_in as [ys [y_in ys_in]].
        apply in_image_iff in ys_in.
        destruct ys_in as [x [ys_is x_in]].
        subst ys.
        apply in_image_iff in y_in.
        destruct y_in as [f_i [y_is f_i_in]].
        subst y.
        exists (image (fun x' : D => proj1_sig f_i x') X)...
    }
    assert (claim6 : isSupremum (f sup_X) (image_sup (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X))).
    { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
      intros ys ys_in.
      apply in_image_iff in ys_in.
      destruct ys_in as [x [ys_is x_in_X]].
      subst ys.
      exists (f x).
      intros y.
      split.
      - intros f_x_le_y y' y'_in.
        apply in_image_iff in y'_in.
        destruct y'_in as [f_i [y'_is f_i_in]].
        subst y'.
        apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x)))...
      - intros y_is_an_upper_bound.
        assert (f_i_sup_X_isSupremum : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x))).
        apply f_i_sup_X_isSupremum...
    }
    assert (claim7 : isSupremum (f sup_X) (image f X)).
    { intros y.
      split.
      - intros f_sup_X_le_y y' y'_in.
        apply in_image_iff in y'_in.
        destruct y'_in as [x [y'_is x_in]].
        subst y'.
        apply claim6...
        exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F).
        split...
        apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x))).
      - intros y_is_an_upper_bound.
        apply claim6.
        intros y' [ys [ys_in y'_isSupremum_of_ys]].
        apply in_image_iff in ys_in.
        destruct ys_in as [x [ys_is x_in_X]].
        subst ys.
        assert (f_x_isSupremum : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x))).
        assert (y'_eq_f_x : y' == f x) by now apply (isSupremum_unique (image (fun f_i : D ~> D' => proj1_sig f_i x) F)).
        transitivity (f x)...
    }
    exists sup_X, (f sup_X)...
  Qed.

  Definition sup_of_set_of_squigs {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : forall F : ensemble (D ~> D'), isDirected F -> (D ~> D') :=
    fun F : ensemble (D ~> D') =>
    fun F_isDirected : isDirected F =>
    exist isContinuousMap (fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x))) (sup_of_set_of_squigs_exists_if_it_is_directed F F_isDirected)
  .

  Lemma sup_of_set_of_squigs_isSupremum {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    isSupremum (sup_of_set_of_squigs F F_isDirected) F.
  Proof with eauto with *.
    intros F F_isDirected f.
    split.
    - intros le_f f' f'_in.
      assert (claim1 : forall x : D, proj1_sig f' x =< proj1_sig (sup_of_set_of_squigs F F_isDirected) x).
      { intros x.
        unfold sup_of_set_of_squigs.
        simpl.
        destruct (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x)) as [sup_F_x sup_F_x_isSupremum].
        simpl.
        apply sup_F_x_isSupremum...
      }
      transitivity (sup_of_set_of_squigs F F_isDirected)...
    - intros f_is_an_upper_bound x.
      unfold sup_of_set_of_squigs.
      simpl.
      destruct (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (sup_of_set_of_squigs_is_well_defined F F_isDirected x)) as [sup_F_x sup_F_x_isSupremum].
      simpl.
      apply sup_F_x_isSupremum.
      intros y y_in.
      apply in_image_iff in y_in.
      destruct y_in as [f_i [f_i_is f_i_in]].
      subst y.
      apply f_is_an_upper_bound...
  Qed.

  Lemma bot_of_squigs_isContinuous {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    isContinuousMap (fun _ : D => proj1_sig bottom_exists).
  Proof with eauto with *.
    intros Y Y_isOpen.
    split.
    - intros x1 x2 x1_in x1_le_x2.
      apply (in_preimage_iff x1) in x1_in...
    - intros X [[x0 x0_in_X] X_closed_under_le] sup_X sup_X_isSupremum_of_X sup_X_in.
      apply (in_preimage_iff sup_X) in sup_X_in...
  Qed.

  Definition bot_of_squigs {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : D ~> D' :=
    exist isContinuousMap (fun _ : D => proj1_sig (@bottom_exists D' D'_isPoset D'_isCompletePartialOrder)) bot_of_squigs_isContinuous
  .

  Lemma bot_of_squigs_isBottom {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D ~> D',
    bot_of_squigs =< f.
  Proof with eauto with *.
    unfold bot_of_squigs.
    intros f x.
    simpl.
    destruct bottom_exists as [bot_D' bot_D'_isBottom]...
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

  Lemma separately_continuous_iff {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) -> D3,
    (forall x1_1 : D1, forall x1_2 : D1, forall x2_1 : D2, forall x2_2 : D2, x1_1 == x1_2 -> x2_1 == x2_2 -> f (x1_1, x2_1) == f (x1_2, x2_2)) ->
    ((forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2))) /\ (forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2)))) <-> isContinuousMap f.
  Proof with eauto with *.
    intros f f_preserves_eq.
    split.
    - intros [f1_continuous f2_continuous].
      apply (the_main_reason_for_introducing_ScottTopology f).
      + intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2]...
      + intros X X_isDirected.
        destruct (square_up_exists X X_isDirected) as [[sup_X1 sup_X2] sup_X_isSupremum_of_X].
        set (X1 := image fst X).
        set (X2 := image snd X).
        assert (claim1 : isDirected X1).
        { destruct X_isDirected as [[[x1_0 x2_0] x0_in_X] X_closed_under_le].
          split.
          - exists x1_0...
          - intros x1 x1_in x2 x2_in.
            apply in_image_iff in x1_in, x2_in.
            destruct x1_in as [[x1_1 x2_1] [Heq1 x1_in_X]].
            destruct x2_in as [[x1_2 x2_2] [Heq2 x2_in_X]].
            subst x1 x2.
            destruct (X_closed_under_le (x1_1, x2_1) x1_in_X (x1_2, x2_2) x2_in_X) as [[x3_1 x3_2] [H8 [[H9 H10] [H11 H12]]]].
            simpl in *...
        }
        assert (claim2 : isDirected X2).
        { destruct X_isDirected as [[[x1_0 x2_0] x0_in_X] X_closed_under_le].
          split.
          - exists x2_0...
          - intros x1 x1_in x2 x2_in.
            apply in_image_iff in x1_in, x2_in.
            destruct x1_in as [[x1_1 x2_1] [Heq1 x1_in_X]].
            destruct x2_in as [[x1_2 x2_2] [Heq2 x2_in_X]].
            subst x1 x2.
            destruct (X_closed_under_le (x1_1, x2_1) x1_in_X (x1_2, x2_2) x2_in_X) as [[x3_1 x3_2] [H8 [[H9 H10] [H11 H12]]]].
            simpl in *...
        }
        assert ( claim3 :
          forall x1 : D1,
          exists sup_X2_x1 : D2, exists sup_f_X2_x1 : D3, isSupremum sup_X2_x1 X2 /\ isSupremum sup_f_X2_x1 (image (fun x2 : D2 => f (x1, x2)) X2) /\ f (x1, sup_X2_x1) == sup_f_X2_x1
        ).
        { intros x1.
          apply the_main_reason_for_introducing_ScottTopology.
          - intros x2_1 x2_2 Heq...
          - apply f1_continuous.
          - apply claim2.
        }
        assert ( claim4 :
          forall x2 : D2,
          exists sup_X1_x2 : D1, exists sup_f_X1_x2 : D3, isSupremum sup_X1_x2 X1 /\ isSupremum sup_f_X1_x2 (image (fun x1 : D1 => f (x1, x2)) X1) /\ f (sup_X1_x2, x2) == sup_f_X1_x2
        ).
        { intros x1.
          apply the_main_reason_for_introducing_ScottTopology.
          - intros x1_1 x1_2 Heq...
          - apply f2_continuous.
          - apply claim1.
        }
        assert (core_claim1 : isSupremum sup_X1 X1 /\ isSupremum sup_X2 X2).
        { destruct (square_up_exists X1 claim1) as [sup_X1' sup_X1'_isSupremum].
          destruct (square_up_exists X2 claim2) as [sup_X2' sup_X2'_isSupremum].
          assert (sup_X'_isSupremum : isSupremum (sup_X1', sup_X2') X).
          { intros [x1 x2].
            split.
            - intros [H H0] [x1' x2'] H2.
              simpl in *.
              split.
              + apply sup_X1'_isSupremum...
              + apply sup_X2'_isSupremum...
            - intros is_an_upper_bound.
              split.
              + apply sup_X1'_isSupremum.
                intros x1' x1'_in.
                apply in_image_iff in x1'_in.
                destruct x1'_in as [[x0_1 x0_2] [x1'_is x0_in]].
                subst x1'.
                apply is_an_upper_bound...
              + apply sup_X2'_isSupremum.
                intros x2' x2'_in.
                apply in_image_iff in x2'_in.
                destruct x2'_in as [[x0_1 x0_2] [x2'_is x0_in]].
                subst x2'.
                apply is_an_upper_bound...
          }
          assert (core_claim1_aux1 : (sup_X1', sup_X2') == (sup_X1, sup_X2)) by now apply (isSupremum_unique X).
          destruct core_claim1_aux1 as [Heq1 Heq2].
          simpl in *.
          split.
          - apply (proj2 (isSupremum_unique X1 sup_X1' sup_X1'_isSupremum sup_X1) Heq1).
          - apply (proj2 (isSupremum_unique X2 sup_X2' sup_X2'_isSupremum sup_X2) Heq2).
        }
        destruct core_claim1 as [claim5 claim6].
        assert (claim7 : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
        { destruct (claim3 sup_X1) as [sup_X2_x1 [sup_f_X1_x2 [sup_X2_x1_isSupremum [sup_f_X1_x2_isSupremum Heq]]]].
          assert (f_sup_X1_sup_X2_isSupremum : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2) <-> sup_f_X1_x2 == f (sup_X1, sup_X2)) by now apply (isSupremum_unique (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
          apply f_sup_X1_sup_X2_isSupremum.
          transitivity (f (sup_X1, sup_X2_x1)).
          - symmetry...
          - apply f_preserves_eq.
            + reflexivity.
            + apply (isSupremum_unique X2)...
        }
        assert ( claim8 :
          forall x2 : D2,
          member x2 X2 ->
          isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)
        ).
        { intros x2 x2_in.
          destruct (claim4 x2) as [sup_X1' [sup_f_X1_x2' [isSupremum_sup_X1' [isSupremum_sup_f_X1_x2' Heq]]]].
          assert (f_sup_X1_x2_isSupremum : isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1) <-> sup_f_X1_x2' == f (sup_X1, x2)) by now apply (isSupremum_unique (image (fun x1 : D1 => f (x1, x2)) X1)).
          apply f_sup_X1_x2_isSupremum.
          transitivity (f (sup_X1', x2)).
          - symmetry...
          - apply f_preserves_eq.
            + apply (isSupremum_unique X1)...
            + reflexivity.
        }
        assert (claim9 : isSupremum (f (sup_X1, sup_X2)) (image_sup (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
        { intros y.
          split.
          - intros le_y y' [ys [ys_in y'_isSupremum_of_ys]].
            apply in_image_iff in ys_in.
            destruct ys_in as [x2 [ys_is x2_in]].
            subst ys.
            assert (claim9_aux1 : f (sup_X1, x2) =< f (sup_X1, sup_X2)) by now apply (ContinuousMapOnCpos_isMonotonic (fun x2 : D2 => f (sup_X1, x2)) (f1_continuous sup_X1)), claim6.
            apply y'_isSupremum_of_ys...
          - intros y_is_an_upper_bound.
            apply claim7.
            intros y' y'_in.
            apply in_image_iff in y'_in.
            destruct y'_in as [x2 [y'_is x2_in]].
            subst y'.
            apply y_is_an_upper_bound.
            exists (image (fun x1 : D1 => f (x1, x2)) X1).
            split...
        }
        assert (claim10 : isSupremum (f (sup_X1, sup_X2)) (unions (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
        { apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs...
          intros ys ys_in.
          apply in_image_iff in ys_in.
          destruct ys_in as [x2 [ys_is x2_in]].
          subst ys.
          exists (f (sup_X1, x2))...
        }
        assert (claim11 : isSupremum (f (sup_X1, sup_X2)) (image f X)).
        { intros y.
          split.
          - intros le_y y' y'_in.
            apply in_image_iff in y'_in.
            destruct y'_in as [[x1 x2] [y'_is x_in]].
            subst y'.
            apply claim10.
            + apply le_y.
            + exists (image (fun x1' : D1 => f (x1', x2)) X1)...
          - intros y_is_an_upper_bound.
            apply claim10.
            intros y' y'_in.
            apply in_unions_iff in y'_in.
            destruct y'_in as [ys [y'_in ys_in]].
            apply in_image_iff in ys_in.
            destruct ys_in as [x2 [ys_is x2_in]].
            subst ys.
            apply in_image_iff in y'_in.
            destruct y'_in as [x1 [y'_is x1_in]].
            subst y'.
            apply in_image_iff in x1_in.
            destruct x1_in as [[x1_1 x2_1] [x1_is x1_in_X]].
            subst x1.
            apply in_image_iff in x2_in.
            destruct x2_in as [[x1_2 x2_2] [x2_is x2_in_X]].
            subst x2.
            destruct (proj2 X_isDirected (x1_1, x2_1) x1_in_X (x1_2, x2_2) x2_in_X) as [[x1_3 x2_3] [x3_in [[x1_1_le_x1_3 x2_1_le_x2_3] [x1_2_le_x1_3 x2_2_le_x2_3]]]].
            simpl in *.
            assert (claim11_aux1 : f (x1_1, x2_2) =< f (x1_3, x2_3)).
            { transitivity (f (x1_1, x2_3)).
              - apply (ContinuousMapOnCpos_isMonotonic (fun x2 : D2 => f (x1_1, x2)) (f1_continuous x1_1))...
              - apply (ContinuousMapOnCpos_isMonotonic (fun x1 : D1 => f (x1, x2_3)) (f2_continuous x2_3))...
            }
            transitivity (f (x1_3, x2_3))...
        }
        exists (sup_X1, sup_X2), (f (sup_X1, sup_X2))...
    - intros f_continuous.
      assert (f1_monotonic : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2))).
      { intros x1 x2_1 x2_2 Hle.
        apply (ContinuousMapOnCpos_isMonotonic f f_continuous).
        split...
      }
      assert (f2_monotonic : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2))).
      { intros x2 x1_1 x1_2 H1.
        apply (ContinuousMapOnCpos_isMonotonic f f_continuous).
        split...
      }
      assert (mayday : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> f p1 == f p2).
      { intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2].
        simpl in *...
      }
      split.
      + intros x1.
        apply the_main_reason_for_introducing_ScottTopology...
        intros X2 X2_isDirected.
        destruct (square_up_exists X2 X2_isDirected) as [sup_X2 sup_X2_isSupremum].
        set (X := image (fun x2 : D2 => (x1, x2)) X2).
        set (Y := image (fun x2 : D2 => f (x1, x2)) X2).
        assert (claim1 : isDirected X).
        { destruct X2_isDirected as [[x2_0 H0] X2_closed_under_le].
          split.
          - exists (x1, x2_0)...
          - intros [x1_1 x2_1] x1_in_X [x1_2 x2_2] x2_in_X.
            apply in_image_iff in x1_in_X, x2_in_X.
            destruct x1_in_X as [x2 [Heq x2_1_in]].
            apply pair_equal_spec in Heq.
            destruct Heq as [Heq1 Heq2].
            subst x1_1 x2.
            destruct x2_in_X as [x2 [Heq x2_2_in]].
            apply pair_equal_spec in Heq.
            destruct Heq as [Heq1 Heq2].
            subst x1_2 x2.
            destruct (X2_closed_under_le x2_1 x2_1_in x2_2 x2_2_in) as [x2_3 [x2_3_in [x2_1_le_x2_3 x2_2_le_x2_3]]].
            exists (x1, x2_3).
            repeat split...
        }
        destruct (square_up_exists X claim1) as [sup_X sup_X_isSupremum].
        assert (claim2 : (x1, sup_X2) == sup_X).
        { apply (isSupremum_unique X)...
          intros [x_1 x_2].
          split.
          - intros [Hle1 Hle2] [x_1' x_2'] x'_in.
            apply in_image_iff in x'_in.
            destruct x'_in as [x2 [Heq x2_in]].
            apply pair_equal_spec in Heq.
            destruct Heq as [Heq1 Heq2].
            subst x_1' x_2'.
            simpl in *...
          - intros is_an_upper_bound.
            simpl.
            split.
            + destruct X2_isDirected as [[x2_0 x2_0_in] X2_closed_under_le].
              apply (is_an_upper_bound (x1, x2_0))...
            + apply sup_X2_isSupremum.
              intros x_2' x_2'_in.
              apply (is_an_upper_bound (x1, x_2'))...
        }
        assert (claim3 : f (x1, sup_X2) == f sup_X) by now apply mayday.
        assert (core_claim2 : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' == sup_Y').
        { apply the_main_reason_for_introducing_ScottTopology.
          - intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2]...
          - apply f_continuous.
          - apply claim1.
        }
        destruct core_claim2 as [sup_X' [sup_Y' [sup_X'_isSupremum [sup_Y'_isSupremum f_x1_sup_X'_eq_sup_Y']]]].
        assert (claim4 : isSupremum (f sup_X) (image f X) <-> sup_Y' == f sup_X) by now apply (isSupremum_unique (image f X)).
        assert (claim5 : isSupremum (f sup_X) (image f X)).
        { apply claim4.
          transitivity (f sup_X').
          - symmetry...
          - assert (claim5_aux1 : sup_X' == sup_X) by now apply (isSupremum_unique X).
            apply mayday...
        }
        assert (claim6 : forall y : D3, member y (image f X) <-> member y Y).
        { intros y.
          split.
          - intros y_in.
            apply in_image_iff in y_in.
            destruct y_in as [[x1_1 x2_1] [y_is x1_in]].
            subst y.
            apply in_image_iff in x1_in.
            destruct x1_in as [x2 [Heq x2_in]].
            rewrite Heq...
          - intros y_in.
            apply in_image_iff in y_in.
            destruct y_in as [x2 [y_is x2_in]].
            subst y...
        }
        assert (claim7 : isSupremum (f sup_X) Y) by now apply (proj2 (isSupremum_ext _ _ claim6 _ claim5 _)).
        exists sup_X2, (f sup_X)...
      + intros x2.
        apply the_main_reason_for_introducing_ScottTopology...
        intros X1 X1_isDirected.
        destruct (square_up_exists X1 X1_isDirected) as [sup_X1 sup_X1_isSupremum].
        set (X := image (fun x1 : D1 => (x1, x2)) X1).
        set (Y := image (fun x1 : D1 => f (x1, x2)) X1).
        assert (claim1 : isDirected X).
        { destruct X1_isDirected as [[x1_0 x1_0_in] X1_closed_under_le].
          split.
          - exists (x1_0, x2)...
          - intros [x1_1 x2_1] x1_in_X [x1_2 x2_2] x2_in_X.
            apply in_image_iff in x1_in_X, x2_in_X.
            destruct x1_in_X as [x1 [Heq x1_1_in]].
            apply pair_equal_spec in Heq.
            destruct Heq as [Heq1 Heq2].
            subst x1 x2_1.
            destruct x2_in_X as [x1 [Heq x1_2_in]].
            apply pair_equal_spec in Heq.
            destruct Heq as [Heq1 Heq2].
            subst x1 x2_2.
            destruct (X1_closed_under_le x1_1 x1_1_in x1_2 x1_2_in) as [x1_3 [x1_3_in [x1_1_le_x1_3 x1_2_le_x1_3]]].
            exists (x1_3, x2).
            repeat split...
        }
        destruct (square_up_exists X claim1) as [sup_X sup_X_isSupremum].
        assert (claim2 : (sup_X1, x2) == sup_X).
        { apply (isSupremum_unique X)...
          intros [x_1 x_2].
          split.
          - intros [H3 H4] [x_1' x_2'] x'_in.
            apply in_image_iff in x'_in.
            destruct x'_in as [x1 [Heq x1_in]].
            apply pair_equal_spec in Heq.
            destruct Heq as [Heq1 Heq2].
            subst x_1' x_2'.
            simpl in *...
          - intros is_an_upper_bound.
            simpl.
            split.
            + apply sup_X1_isSupremum.
              intros x_1' x_1'_in.
              apply (is_an_upper_bound (x_1', x2))...
            + destruct X1_isDirected as [[x1_0 x1_0_in] X1_closed_under_le].
              apply (is_an_upper_bound (x1_0, x2))...
        }
        assert (claim3 : f (sup_X1, x2) == f sup_X) by now apply mayday.
        assert (core_claim3 : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' == sup_Y').
        { apply the_main_reason_for_introducing_ScottTopology.
          - intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2]...
          - apply f_continuous.
          - apply claim1.
        }
        destruct core_claim3 as [sup_X' [sup_Y' [sup_X'_isSupremum [sup_Y'_isSupremum f_sup_X'_eq_sup_Y']]]].
        assert (claim4 : isSupremum (f sup_X) (image f X) <-> sup_Y' == f sup_X) by now apply (isSupremum_unique (image f X)).
        assert (claim5 : isSupremum (f sup_X) (image f X)).
        { apply claim4.
          transitivity (f sup_X').
          - symmetry...
          - assert (claim5_aux1 : sup_X' == sup_X) by now apply (isSupremum_unique X).
            apply mayday...
        }
        assert (claim6 : forall y : D3, member y (image f X) <-> member y Y).
        { intros y.
          split.
          - intros y_in.
            apply in_image_iff in y_in.
            destruct y_in as [[x1_1 x2_1] [y_is x1_in]].
            subst y.
            apply in_image_iff in x1_in.
            destruct x1_in as [x1 [Heq x1_in]].
            rewrite Heq...
          - intros y_in.
            apply in_image_iff in y_in.
            destruct y_in as [x1 [y_is x1_in]].
            subst y...
        }
        assert (claim7 : isSupremum (f sup_X) Y) by apply (proj2 (isSupremum_ext _ _ claim6 _ claim5 _) (Setoid_refl _)).
        exists sup_X1, (f sup_X)...
  Qed.

  Lemma ScottApp_isMontonic {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    isMonotonicMap (@uncurry (D ~> D') D D' (@proj1_sig (D -> D') isContinuousMap)).
  Proof with eauto with *.
    intros [f1 x1] [f2 x2] [H H0].
    simpl in *.
    assert (claim1 : isContinuousMap (proj1_sig f1)) by membership.
    transitivity (proj1_sig f1 x2); [apply ContinuousMapOnCpos_isMonotonic | apply H]...
  Qed.

  Definition ScottApp {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) (D'_requiresCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset) : ((D ~> D') * D) >=> D' :=
    exist _ (@uncurry (D ~> D') D D' (@proj1_sig (D -> D') isContinuousMap)) ScottApp_isMontonic
  .

  Lemma ScottApp_preserves_eq {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f1 : D ~> D',
    forall f2 : D ~> D',
    forall x1 : D,
    forall x2 : D,
    f1 == f2 ->
    x1 == x2 ->
    proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (f1, x1) == proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (f2, x2).
  Proof with (membership || eauto with *).
    intros f1 f2 x1 x2 Heq_f Heq_x.
    simpl.
    transitivity (proj1_sig f1 x2).
    - apply Poset_asym; apply ContinuousMapOnCpos_isMonotonic...
    - apply Heq_f.
  Qed.

  Lemma ScottApp_isContinuous {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    isContinuousMap (proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder)).
  Proof with (membership || eauto with *).
    apply (separately_continuous_iff (proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder)) ScottApp_preserves_eq).
    split.
    - unfold ScottApp.
      simpl.
      intros f...
    - intros x.
      assert (mayday : isMonotonicMap (fun f : D ~> D' => proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (f, x))).
      { intros f1 f2 f1_le_f2.
        unfold ScottApp...
      }
      apply the_main_reason_for_introducing_ScottTopology.
      + intros f1 f2 Heq_f.
        apply ScottApp_preserves_eq...
      + intros fs fs_isDirected.
        set (Y := image (fun f_i : D ~> D' => proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (f_i, x)) fs).
        set (f := fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_set_of_squigs_is_well_defined fs fs_isDirected x))).
        set (sup_fs := exist isContinuousMap f (sup_of_set_of_squigs_exists_if_it_is_directed fs fs_isDirected)).
        assert (claim1 : forall x : D, isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) fs)) by apply (fun x : D => proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) fs) (sup_of_set_of_squigs_is_well_defined fs fs_isDirected x))).
        assert (claim2 : isSupremum sup_fs fs).
        { intros g.
          split.
          - intros H g' H0 x'.
            apply (claim1 x')...
          - intros H x'.
            apply (claim1 x').
            intros g' H0.
            apply in_image_iff in H0.
            destruct H0 as [f_i [g'_is f_i_in]].
            subst g'.
            apply (H f_i)...
        }
        assert (claim3 : isSupremum (proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (sup_fs, x)) Y).
        { intros y.
          split.
          - intros le_y y' y'_in.
            apply (claim1 x)...
          - intros y_is_an_upper_bound.
            apply (claim1 x)...
        }
        exists sup_fs, (proj1_sig (ScottApp D_isCompletePartialOrder D'_isCompletePartialOrder) (sup_fs, x))...
  Qed.

End ClassicalCpoTheory.
