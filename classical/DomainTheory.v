Require Import Coq.Lists.List.
Require Import DschingisKhan.classical.ExclusiveMiddle.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module ClassicalCpoTheory. (* Reference: "The Lambda Calculus: Its Syntax and Semantics" of "H. P. Barendregt." *)

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble MyEnsembleNova BasicPosetTheory BasicTopology ConstructiveCpoTheory ExclusiveMiddle.

  Definition U {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D :=
    fun x : D =>
    fun z : D =>
    ~ z =< x
  .

  Global Hint Unfold U : my_hints.

  Lemma U_x_isOpen {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} :
    forall x : D,
    isOpen (U x).
  Proof with tauto. (* Thanks to Junyoung Jang *)
    intros x.
    split.
    - intros y z y_in_U_x y_le_z z_le_x.
      contradiction y_in_U_x.
      transitivity z...
    - intros X X_isDirected sup_X sup_X_isSupremum_of_X sup_X_in_U_x.
      assert (JunyoungJang'sAdvice : ~ (forall x0 : D, member x0 X -> x0 =< x)).
      { intros x_is_an_upper_bound_of_X.
        contradiction sup_X_in_U_x.
        exact (proj2 (sup_X_isSupremum_of_X x) x_is_an_upper_bound_of_X).
      }
      destruct (not_all_ex_not D (fun x0 : D => member x0 X -> x0 =< x) JunyoungJang'sAdvice) as [x0 x0_is_a_member_of_X_which_is_less_than_or_equal_to_x].
      exists x0.
      apply in_intersection_iff.
      destruct (classic (member x0 X /\ ~ x0 =< x))...
  Qed.

  Lemma ContinuousMap_isMonotonicMap {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    isContinuousMap f ->
    isMonotonicMap f.
  Proof.
    intros f f_continuous x1 x2 x1_le_x2.
    apply NNPP.
    intros f_x1_le_f_x2_is_false.
    assert (f_x1_in_U_f_x2 : member (f x1) (U (f x2))) by exact f_x1_le_f_x2_is_false.
    assert (x1_in_preimage_f_U_f_x2 : member x1 (preimage f (U (f x2)))) by now constructor.
    assert (preimage_f_U_f_x2_isOpen : isOpen (preimage f (U (f x2)))) by now apply f_continuous, U_x_isOpen.
    assert (x2_in_preimage_f_U_f_x2 : member x2 (preimage f (U (f x2)))) by now apply (proj1 preimage_f_U_f_x2_isOpen x1 x2).
    assert (f_x2_in_U_f_x2 : member (f x2) (U (f x2))) by now inversion x2_in_preimage_f_U_f_x2; subst.
    now contradiction f_x2_in_U_f_x2.
  Qed.

  Lemma MonotonicMap_preservesDirected {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} :
    forall f : D -> D',
    isMonotonicMap f ->
    forall X : ensemble D,
    isDirected X ->
    isDirected (image f X).
  Proof with eauto with *.
    intros f f_monotonic X [[x0 x0_in_X] X_closed_under_le].
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

  Lemma f_sup_X_eq_square_up_image_f_X {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
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
    assert (f_monotonic : forall x1 : D, forall x2 : D, x1 =< x2 -> f x1 =< f x2) by now apply ContinuousMap_isMonotonicMap.
    set (Y := image f X).
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
      assert (f_x1_in_U_sup_Y : member (f x1) (U sup_Y)) by now apply (in_preimage_iff x1).
      contradiction f_x1_in_U_sup_Y.
      apply sup_Y_isSupremum_of_Y...
    }
    apply Poset_asym...
  Qed.

  Lemma isSupremum_of_image_f_X_iff_f_sup_X_eq {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
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
    assert (image_f_X_isDirected : isDirected (image f X)).
    { apply MonotonicMap_preservesDirected.
      - exact (ContinuousMap_isMonotonicMap f f_continuous).
      - exact X_isDirected.
    }
    assert (claim1 := square_up_isSupremum (image f X) image_f_X_isDirected).
    assert (claim2 := f_sup_X_eq_square_up_image_f_X f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X image_f_X_isDirected).
    assert (claim3 := square_up_isSupremum (image f X) (image_f_X_isDirected)).
    split.
    - transitivity (proj1_sig (square_up_exists (image f X) image_f_X_isDirected)).
      + exact (f_sup_X_eq_square_up_image_f_X f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X image_f_X_isDirected).
      + apply (isSupremum_unique (image f X))...
    - intros f_sup_X_eq_sup_Y.
      apply (proj2 (isSupremum_unique (image f X) (proj1_sig (square_up_exists (image f X) image_f_X_isDirected)) claim3 sup_Y))...
  Qed.

  Global Hint Resolve isSupremum_of_image_f_X_iff_f_sup_X_eq : my_hints.

  Lemma ContinuousMapsOnCpos_preservesSupremum {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    isContinuousMap f ->
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    isSupremum (f sup_X) (image f X).
  Proof.
    intros f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X.
    now apply (proj2 (isSupremum_of_image_f_X_iff_f_sup_X_eq f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X (f sup_X))).
  Qed.

  Definition preservesSupremum {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : (D -> D') -> Prop :=
    fun f : D -> D' =>
    forall X : ensemble D,
    @isDirected D D_isPoset X ->
    exists sup_X : D, exists sup_Y : D', @isSupremum D D_isPoset sup_X X /\ @isSupremum D' D'_isPoset sup_Y (image f X) /\ @eqProp D' (@Poset_requiresSetoid D' D'_isPoset) (f sup_X) sup_Y
  .

  Lemma isMonotonicMap_if_preservesSupremum {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    (forall x1 : D, forall x2 : D, x1 == x2 -> f x1 == f x2) ->
    preservesSupremum f ->
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
    assert (it_is_sufficient_to_show : f sup_X == f x2) by now apply f_preserves_eq, (isSupremum_unique X).
    transitivity (sup_Y)...
  Qed.

  Lemma show_image_f_X_isDirected_if_f_satisfies_preservesSupremum_and_X_isDirected {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    (forall x1 : D, forall x2 : D, x1 == x2 -> f x1 == f x2) ->
    preservesSupremum f -> 
    forall X : ensemble D,
    isDirected X ->
    isDirected (image f X).
  Proof with eauto with *.
    intros f f_preserves_eq f_property X X_isDirected.
    assert (claim1 := isMonotonicMap_if_preservesSupremum f f_preserves_eq f_property).
    destruct X_isDirected as [[x1_0 x1_0_in_X] X_closed_under_le].
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
  Qed.

  Theorem the_main_reason_for_introducing_ScottTopology {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D -> D',
    (forall x1 : D, forall x2 : D, x1 == x2 -> f x1 == f x2) ->
    isContinuousMap f <-> preservesSupremum f.
  Proof with eauto with *.
    assert (claim1 : forall f : D >=> D', isContinuousMap (proj1_sig f) -> forall x1 : D, forall x2 : D, x1 =< x2 -> proj1_sig f x1 =< proj1_sig f x2) by apply (fun f : D >=> D' => ContinuousMap_isMonotonicMap (proj1_sig f)).
    intros f f_preserves_eq.
    split.
    - intros f_continuous X X_isDirected.
      set (Y := image f X).
      assert (claim2 : isDirected Y).
      { apply MonotonicMap_preservesDirected.
        - exact (ContinuousMap_isMonotonicMap f f_continuous).
        - exact X_isDirected.
      }
      destruct (square_up_exists X X_isDirected) as [sup_X sup_X_isSupremum_of_X].
      assert (claim3 := ContinuousMapsOnCpos_preservesSupremum f f_continuous X X_isDirected sup_X sup_X_isSupremum_of_X).
      exists sup_X, (f sup_X)...
    - intros f_property.
      assert (claim4 := isMonotonicMap_if_preservesSupremum f f_preserves_eq f_property).
      intros O O_isOpen.
      split.
      + intros x1 x2 x_in_preimage_f_O x_le_y.
        apply (in_preimage_iff x1) in x_in_preimage_f_O.
        constructor.
        apply (proj1 O_isOpen (f x1) (f x2))...
      + intros X X_isDirected sup_X sup_X_isSupremum_of_X sup_X_in_preimage_f_O.
        destruct (f_property X X_isDirected) as [sup_X' [sup_Y' [sup_X'_isSupremum_of_X [sup_Y'_isSupremum_of_image_f_X f_sup_X'_eq_sup_Y']]]].
        assert (sup_X_eq_sup_X' : sup_X == sup_X') by now apply (isSupremum_unique X).
        assert (f_sup_X_in_O : member (f sup_X) O) by now apply (in_preimage_iff sup_X).
        assert (claim5 := show_image_f_X_isDirected_if_f_satisfies_preservesSupremum_and_X_isDirected f f_preserves_eq f_property X X_isDirected).
        assert (claim6 : sup_Y' == f sup_X).
        { transitivity (f sup_X').
          - symmetry...
          - apply f_preserves_eq...
        }
        assert (claim7 : nonempty (intersection (image f X) O)).
        { apply (proj2 O_isOpen (image f X) claim5 (f sup_X))...
          apply (isSupremum_unique (image f X) sup_Y' sup_Y'_isSupremum_of_image_f_X)...
        }
        destruct claim7 as [y y_in_image_f_X_and_O].
        apply in_intersection_iff in y_in_image_f_X_and_O.
        destruct y_in_image_f_X_and_O as [y_in_image_f_X y_in_O].
        apply in_image_iff in y_in_image_f_X.
        destruct y_in_image_f_X as [x [y_eq_f_x x_in_X]].
        subst y...
  Qed.

  Global Instance set_of_ContinuousMap_isPoset {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) (D'_requiresCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset) : isPoset (@sig (D -> D') (@isContinuousMap D D' (ScottTopology D_requiresCompletePartialOrder) (ScottTopology D'_requiresCompletePartialOrder))) :=
    @SubPoset (D -> D') (@isContinuousMap D D' (ScottTopology D_requiresCompletePartialOrder) (ScottTopology D'_requiresCompletePartialOrder)) (arrow_isPoset D'_isPoset)
  .

  Definition squig_isMonotonicMap {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : (D ~> D') -> (D >=> D') :=
    fun f : D ~> D' =>
    exist isMonotonicMap (proj1_sig f) (ContinuousMap_isMonotonicMap (proj1_sig f) (proj2_sig f))
  .

  Lemma Supremum_of_squigs_is_well_defined {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    isDirected F ->
    forall x : D,
    isDirected (image (fun f_i : D ~> D' => proj1_sig f_i x) F).
  Proof with eauto with *.
    intros F [nonempty_F F_closed_under_le] x.
    split.
    - destruct nonempty_F as [f0 f0_in]...
    - intros y1 y1_in y2 y2_in.
      apply in_image_iff in y1_in, y2_in.
      destruct y1_in as [f1 [y1_is f1_in]].
      destruct y2_in as [f2 [y2_is f2_in]].
      subst y1 y2.
      destruct (F_closed_under_le f1 f1_in f2 f2_in) as [f3 [f3_in [f1_le_f3 f2_le_f3]]].
      exists (proj1_sig f3 x).
      repeat split...
  Qed.

  Definition Supremum_of_squigs {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : forall F : ensemble (D ~> D'), isDirected F -> (D -> D') :=
    fun F : ensemble (D ~> D') =>
    fun F_isDirected : isDirected F =>
    fun x : D =>
    proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (Supremum_of_squigs_is_well_defined F F_isDirected x))
  .

  Lemma Supremum_of_squigs_isMonotonic {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    isMonotonicMap (fun x : D => Supremum_of_squigs F F_isDirected x).
  Proof with eauto with *.
    intros F F_isDirected x1 x2 x1_le_x2.
    apply (square_up_isSupremum (image (fun f_i : D ~> D' => proj1_sig f_i x1) F) (Supremum_of_squigs_is_well_defined F F_isDirected x1)).
    intros y y_in.
    apply in_image_iff in y_in.
    destruct y_in as [f_i [y1_is f_i_in]].
    subst y.
    transitivity (proj1_sig f_i x2).
    - apply (ContinuousMap_isMonotonicMap (proj1_sig f_i) (proj2_sig f_i))...
    - apply (square_up_isSupremum (image (fun f_i : D ~> D' => proj1_sig f_i x2) F) (Supremum_of_squigs_is_well_defined F F_isDirected x2))...
  Qed.

  Lemma Supremum_of_squigs_sup_X_isSupremum_unions_i_image_f_i_X_F {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    isSupremum (Supremum_of_squigs F F_isDirected sup_X) (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) F)).
  Proof with eauto with *.
    intros F F_isDirected X X_isDirected sup_X sup_X_isSupremum_of_X.
    assert ( claim1 :
      forall f_i : D ~> D',
      member f_i F ->
      isSupremum (proj1_sig f_i sup_X) (image (fun x : D => proj1_sig f_i x) X)
    ).
    { intros f_i f_i_in.
      apply (isSupremum_of_image_f_X_iff_f_sup_X_eq (proj1_sig f_i) (proj2_sig f_i) X X_isDirected sup_X sup_X_isSupremum_of_X)...
    }
    assert (claim2 : isSupremum (Supremum_of_squigs F F_isDirected sup_X) (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) F)) by now apply (square_up_isSupremum (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) F) (Supremum_of_squigs_is_well_defined F F_isDirected sup_X)).
    apply isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs.
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
        assert (f_i_sup_X_isSupremum := claim1 f_i f_i_in).
        assert (y'_eq : y' == proj1_sig f_i sup_X) by now apply (isSupremum_unique (image (fun x : D => proj1_sig f_i x) X)).
        assert (f_i_sup_X_in : member (proj1_sig f_i sup_X) (image (fun f_i0 : D ~> D' => proj1_sig f_i0 sup_X) F))...
      + intros y_is_an_upper_bound.
        apply claim2.
        intros y' y'_in.
        apply in_image_iff in y'_in.
        destruct y'_in as [f_i [y'_is f_i_in]].
        subst y'.
        apply y_is_an_upper_bound.
        exists (image (fun x : D => proj1_sig f_i x) X).
        split...
  Qed.

  Lemma lemma1_on_Supremum_commutation {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    isDirected F ->
    forall X : ensemble D,
    isDirected X ->
    forall y : D',
    isSupremum y (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) F)) <-> isSupremum y (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X)).
  Proof with eauto with *.
    intros F F_isDirected X X_isDirected.
    set (Y := unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) F)).
    set (Y' := unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X)).
    assert (claim1 : forall y : D', member y Y <-> member y Y').
    { intros y.
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
    assert (claim2 : forall y : D', member y Y' <-> member y Y) by firstorder.
    intros y.
    split.
    + intros y_isSupremum.
      apply (isSupremum_ext Y Y' claim1 y y_isSupremum)...
    + intros y_isSupremum.
      apply (isSupremum_ext Y' Y claim2 y y_isSupremum)...
  Qed.

  Lemma lemma2_on_Supremum_commutation {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    isDirected F ->
    forall X : ensemble D,
    isDirected X ->
    forall y0 : D',
    isSupremum y0 (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X)) <-> isSupremum y0 (image_sup (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X)).
  Proof with eauto with *.
    intros F F_isDirected X X_isDirected.
    apply (isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X)).
    destruct (square_up_exists X X_isDirected) as [sup_X sup_X_isSupremum_of_X].
    set (f := fun x : D => Supremum_of_squigs F F_isDirected x).
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
      apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (Supremum_of_squigs_is_well_defined F F_isDirected x)))...
    - intros y_is_an_upper_bound.
      assert (f_i_sup_X_isSupremum : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (Supremum_of_squigs_is_well_defined F F_isDirected x))).
      apply f_i_sup_X_isSupremum...
  Qed.

  Lemma Supremum_of_squigs_preservesSupremum {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    isSupremum (Supremum_of_squigs F F_isDirected sup_X) (image (Supremum_of_squigs F F_isDirected) X).
  Proof with eauto with *.
    intros F F_isDirected.
    set (f := fun x : D => Supremum_of_squigs F F_isDirected x).
    assert (claim1 := Supremum_of_squigs_isMonotonic F F_isDirected).
    intros X X_isDirected sup_X sup_X_isSupremum_of_X.
    set (Y := image f X).
    assert ( claim2 :
      forall f_i : D ~> D',
      member f_i F ->
      isSupremum (proj1_sig f_i sup_X) (image (fun x : D => proj1_sig f_i x) X)
    ).
    { intros f_i f_i_in.
      apply (isSupremum_of_image_f_X_iff_f_sup_X_eq (proj1_sig f_i) (proj2_sig f_i) X X_isDirected sup_X sup_X_isSupremum_of_X)...
    }
    assert (claim3 : isSupremum (f sup_X) (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i sup_X) F) (Supremum_of_squigs_is_well_defined F F_isDirected sup_X))).
    assert (claim4 : isSupremum (f sup_X) (unions (image (fun f_i : D ~> D' => image (fun x : D => proj1_sig f_i x) X) F))) by now apply Supremum_of_squigs_sup_X_isSupremum_unions_i_image_f_i_X_F.
    assert (claim5 : isSupremum (f sup_X) (unions (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X))) by now apply lemma1_on_Supremum_commutation.
    assert (claim6 : isSupremum (f sup_X) (image_sup (image (fun x : D => image (fun f_i : D ~> D' => proj1_sig f_i x) F) X))) by now apply lemma2_on_Supremum_commutation.
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
        exact (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (Supremum_of_squigs_is_well_defined F F_isDirected x))).
      - intros y_is_an_upper_bound.
        apply claim6.
        intros y' [ys [ys_in y'_isSupremum_of_ys]].
        apply in_image_iff in ys_in.
        destruct ys_in as [x [ys_is x_in_X]].
        subst ys.
        assert (f_x_isSupremum : isSupremum (f x) (image (fun f_i : D ~> D' => proj1_sig f_i x) F)) by apply (proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (Supremum_of_squigs_is_well_defined F F_isDirected x))).
        assert (y'_eq_f_x : y' == f x) by now apply (isSupremum_unique (image (fun f_i : D ~> D' => proj1_sig f_i x) F)).
        transitivity (f x)...
    }
    exact claim7.
  Qed.

  Lemma Supremum_of_squigs_exists_if_it_is_directed {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    isContinuousMap (fun x : D => Supremum_of_squigs F F_isDirected x).
  Proof with eauto with *.
    intros F F_isDirected.
    set (f := fun x : D => Supremum_of_squigs F F_isDirected x).
    assert (claim1 := Supremum_of_squigs_isMonotonic F F_isDirected).
    fold f in claim1.
    apply (the_main_reason_for_introducing_ScottTopology f (MonotonicMap_preservesSetoid f claim1)).
    intros X X_isDirected.
    set (Y := image f X).
    destruct (square_up_exists X X_isDirected) as [sup_X sup_X_isSupremum_of_X].
    assert (claim2 := Supremum_of_squigs_preservesSupremum F F_isDirected X X_isDirected sup_X sup_X_isSupremum_of_X).
    exists sup_X, (f sup_X)...
  Qed.

  Definition square_up_of_squigs {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : forall F : ensemble (D ~> D'), isDirected F -> (D ~> D') :=
    fun F : ensemble (D ~> D') =>
    fun F_isDirected : isDirected F =>
    exist isContinuousMap (fun x : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (Supremum_of_squigs_is_well_defined F F_isDirected x))) (Supremum_of_squigs_exists_if_it_is_directed F F_isDirected)
  .

  Lemma square_up_of_squigs_isSupremum {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall F : ensemble (D ~> D'),
    forall F_isDirected : isDirected F,
    isSupremum (square_up_of_squigs F F_isDirected) F.
  Proof with eauto with *.
    intros F F_isDirected.
    split.
    - intros le_f f' f'_in.
      assert (claim1 : forall x : D, proj1_sig f' x =< proj1_sig (square_up_of_squigs F F_isDirected) x).
      { intros x.
        unfold square_up_of_squigs.
        simpl.
        destruct (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (Supremum_of_squigs_is_well_defined F F_isDirected x)) as [sup_F_x sup_F_x_isSupremum].
        simpl.
        apply sup_F_x_isSupremum...
      }
      transitivity (square_up_of_squigs F F_isDirected)...
    - intros f_is_an_upper_bound x.
      unfold square_up_of_squigs.
      simpl.
      destruct (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x) F) (Supremum_of_squigs_is_well_defined F F_isDirected x)) as [sup_F_x sup_F_x_isSupremum].
      simpl.
      apply sup_F_x_isSupremum.
      intros y y_in.
      apply in_image_iff in y_in.
      destruct y_in as [f_i [f_i_is f_i_in]].
      subst y.
      apply f_is_an_upper_bound...
  Qed.

  Lemma bot_of_squigs_isContinuousMap {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    isContinuousMap (fun _ : D => proj1_sig bottom_exists).
  Proof with eauto with *.
    intros O O_isOpen.
    split.
    - intros x1 x2 x1_in x1_le_x2.
      apply (in_preimage_iff x1) in x1_in...
    - intros X [[x0 x0_in_X] X_closed_under_le] sup_X sup_X_isSupremum_of_X sup_X_in.
      apply (in_preimage_iff sup_X) in sup_X_in...
  Qed.

  Definition bot_of_squigs {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : D ~> D' :=
    exist isContinuousMap (fun _ : D => proj1_sig (@bottom_exists D' D'_isPoset D'_isCompletePartialOrder)) (@bot_of_squigs_isContinuousMap D D' D_isPoset D'_isPoset D_isCompletePartialOrder D'_isCompletePartialOrder)
  .

  Lemma bot_of_squigs_isBottom {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f : D ~> D',
    bot_of_squigs =< f.
  Proof.
    exact (fun f : D ~> D' => fun x : D => proj2_sig bottom_exists (proj1_sig f x)).
  Qed.

  Global Instance squig_isCompletePartialOrder {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) (D'_requiresCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset) : @isCompletePartialOrder (D ~> D') (@SubPoset (D -> D') isContinuousMap (arrow_isPoset D'_isPoset)) :=
    { bottom_exists :=
      exist _ bot_of_squigs bot_of_squigs_isBottom
    ; square_up_exists :=
      fun F : ensemble (D ~> D') =>
      fun F_isDirected : isDirected F =>
      exist _ (square_up_of_squigs F F_isDirected) (square_up_of_squigs_isSupremum F F_isDirected)
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

  Lemma f_x1_sup_X2_eq_sup_f_x1_X2 {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) -> D3,
    isContinuousMap f ->
    forall x1 : D1,
    forall X2 : ensemble D2,
    isDirected X2 ->
    forall sup_X2 : D2,
    isSupremum sup_X2 X2 ->
    isSupremum (f (x1, sup_X2)) (image (fun x2 : D2 => f (x1, x2)) X2).
  Proof with eauto with *.
    intros f f_continuous.
    assert (f_monotonic : isMonotonicMap f) by now apply ContinuousMap_isMonotonicMap.
    assert (f1_monotonic : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2))).
    { intros x1 x2_1 x2_2 Hle.
      apply (ContinuousMap_isMonotonicMap f f_continuous).
      split...
    }
    assert (mayday : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> f p1 == f p2).
    { intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2].
      simpl in *.
      apply (MonotonicMap_preservesSetoid f f_monotonic).
      split...
    }
    intros x1.
    assert (aux1 := MonotonicMap_preservesSetoid (fun x2 : D2 => f (x1, x2)) (f1_monotonic x1)).
    intros X2 X2_isDirected.
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
    intros sup_X2 sup_X2_isSupremum.
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
    assert (aux2 : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' == sup_Y').
    { apply the_main_reason_for_introducing_ScottTopology.
      - intros [x1_1 x2_1] [x1_2 x2_2] Heq...
      - apply f_continuous.
      - apply claim1.
    }
    destruct aux2 as [sup_X' [sup_Y' [sup_X'_isSupremum [sup_Y'_isSupremum f_x1_sup_X'_eq_sup_Y']]]].
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
    apply (proj2 (isSupremum_ext (image f X) Y claim6 (f sup_X) claim5 (f (x1, sup_X2))))...
  Qed.

  Lemma show_that_f1_isContinuousMap_if_f_isContinuousMap {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) -> D3,
    isContinuousMap f ->
    forall x1 : D1,
    isContinuousMap (fun x2 : D2 => f (x1, x2)).
  Proof with eauto with *.
    intros f f_continuous.
    assert (f_monotonic : isMonotonicMap f) by now apply ContinuousMap_isMonotonicMap.
    assert (f1_monotonic : forall x1 : D1, isMonotonicMap (fun x2 : D2 => f (x1, x2))).
    { intros x1 x2_1 x2_2 Hle.
      apply (ContinuousMap_isMonotonicMap f f_continuous).
      split...
    }
    assert (mayday : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> f p1 == f p2).
    { intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2].
      simpl in *.
      apply (MonotonicMap_preservesSetoid f f_monotonic).
      split...
    }
    intros x1.
    assert (claim1 := MonotonicMap_preservesSetoid (fun x2 : D2 => f (x1, x2)) (f1_monotonic x1)).
    apply the_main_reason_for_introducing_ScottTopology...
    intros X2 X2_isDirected.
    destruct (square_up_exists X2 X2_isDirected) as [sup_X2 sup_X2_isSupremum].
    assert (claim2 := f_x1_sup_X2_eq_sup_f_x1_X2 f f_continuous x1 X2 X2_isDirected sup_X2 sup_X2_isSupremum)...
  Qed.

  Lemma f_sup_X1_x2_eq_sup_f_X1_x2 {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) -> D3,
    isContinuousMap f ->
    forall x2 : D2,
    forall X1 : ensemble D1,
    isDirected X1 ->
    forall sup_X1 : D1,
    isSupremum sup_X1 X1 ->
    isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1).
  Proof with eauto with *.
    intros f f_continuous.
    assert (f_monotonic : isMonotonicMap f) by now apply ContinuousMap_isMonotonicMap.
    assert (f2_monotonic : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2))).
    { intros x1 x2_1 x2_2 Hle.
      apply (ContinuousMap_isMonotonicMap f f_continuous).
      split...
    }
    assert (mayday : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> f p1 == f p2).
    { intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2].
      simpl in *.
      apply (MonotonicMap_preservesSetoid f f_monotonic).
      split...
    }
    intros x2.
    assert (lemma1 := MonotonicMap_preservesSetoid (fun x1 : D1 => f (x1, x2)) (f2_monotonic x2)).
    intros X1 X1_isDirected.
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
    intros sup_X1 sup_X1_isSupremum.
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
    assert (lemma2 : exists sup_X' : D1 * D2, exists sup_Y' : D3, isSupremum sup_X' X /\ isSupremum sup_Y' (image f X) /\ f sup_X' == sup_Y').
    { apply the_main_reason_for_introducing_ScottTopology.
      - intros [x1_1 x2_1] [x1_2 x2_2] Heq...
      - apply f_continuous.
      - apply claim1.
    }
    destruct lemma2 as [sup_X' [sup_Y' [sup_X'_isSupremum [sup_Y'_isSupremum f_sup_X'_eq_sup_Y']]]].
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
    apply (proj2 (isSupremum_ext (image f X) Y claim6 (f sup_X) claim5 (f (sup_X1, x2))))...
  Qed.

  Lemma show_that_f2_isContinuousMap_if_f_isContinuousMap {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) -> D3,
    isContinuousMap f ->
    forall x2 : D2,
    isContinuousMap (fun x1 : D1 => f (x1, x2)).
  Proof with eauto with *.
    intros f f_continuous.
    assert (f_monotonic : isMonotonicMap f) by now apply ContinuousMap_isMonotonicMap.
    assert (f2_monotonic : forall x2 : D2, isMonotonicMap (fun x1 : D1 => f (x1, x2))).
    { intros x1 x2_1 x2_2 Hle.
      apply (ContinuousMap_isMonotonicMap f f_continuous).
      split...
    }
    assert (mayday : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> f p1 == f p2).
    { intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2].
      simpl in *.
      apply (MonotonicMap_preservesSetoid f f_monotonic).
      split...
    }
    intros x2.
    assert (claim1 := MonotonicMap_preservesSetoid (fun x1 : D1 => f (x1, x2)) (f2_monotonic x2)).
    apply the_main_reason_for_introducing_ScottTopology...
    intros X1 X1_isDirected.
    destruct (square_up_exists X1 X1_isDirected) as [sup_X1 sup_X1_isSupremum].
    assert (claim2 := f_sup_X1_x2_eq_sup_f_X1_x2 f f_continuous x2 X1 X1_isDirected sup_X1 sup_X1_isSupremum)...
  Qed.

  Lemma f_sup_X1_sup_X2_isSupremum_f_X1_X2 {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) -> D3,
    (forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2))) ->
    (forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2))) ->
    forall X : ensemble (D1 * D2),
    isDirected X ->
    forall sup_X1 : D1,
    isSupremum sup_X1 (image fst X) ->
    forall sup_X2 : D2,
    isSupremum sup_X2 (image snd X) ->
    isSupremum (f (sup_X1, sup_X2)) (image f X).
  Proof with eauto with *.
    intros f f1_continuous f2_continuous.
    assert (f1_monotonic := fun x1 : D1 => ContinuousMap_isMonotonicMap (fun x2 : D2 => f (x1, x2)) (f1_continuous x1)).
    assert (f2_monotonic := fun x2 : D2 => ContinuousMap_isMonotonicMap (fun x1 : D1 => f (x1, x2)) (f2_continuous x2)).
    assert (f1_preserves_eq := fun x1 : D1 => MonotonicMap_preservesSetoid (fun x2 : D2 => f (x1, x2)) (f1_monotonic x1)).
    assert (f2_preserves_eq := fun x2 : D2 => MonotonicMap_preservesSetoid (fun x1 : D1 => f (x1, x2)) (f2_monotonic x2)).
    assert (f_preserves_eq : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> f p1 == f p2).
    { intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2].
      simpl in *.
      transitivity (f (x1_1, x2_2))...
    }
    intros X X_isDirected.
    set (X1 := image fst X).
    set (X2 := image snd X).
    set (claim1 := proj1 (directed_subset_of_direct_product X X_isDirected)).
    set (claim2 := proj2 (directed_subset_of_direct_product X X_isDirected)).
    assert (mayday := square_up_of_direct_product X X_isDirected).
    fold claim1 claim2 in mayday.
    fold X1 in claim1, mayday.
    fold X2 in claim2, mayday.
    assert ( claim3 :
      forall x1 : D1,
      exists sup_X2_x1 : D2, exists sup_f_X2_x1 : D3, isSupremum sup_X2_x1 X2 /\ isSupremum sup_f_X2_x1 (image (fun x2 : D2 => f (x1, x2)) X2) /\ f (x1, sup_X2_x1) == sup_f_X2_x1
    ).
    { intros x1.
      apply the_main_reason_for_introducing_ScottTopology...
    }
    assert ( claim4 :
      forall x2 : D2,
      exists sup_X1_x2 : D1, exists sup_f_X1_x2 : D3, isSupremum sup_X1_x2 X1 /\ isSupremum sup_f_X1_x2 (image (fun x1 : D1 => f (x1, x2)) X1) /\ f (sup_X1_x2, x2) == sup_f_X1_x2
    ).
    { intros x2.
      apply the_main_reason_for_introducing_ScottTopology...
    }
    set (sup_X1 := proj1_sig (square_up_exists X1 claim1)).
    set (sup_X2 := proj1_sig (square_up_exists X2 claim2)).
    fold sup_X1 sup_X2 in mayday.
    assert (claim5 := proj2_sig (square_up_exists X1 claim1)).
    assert (claim6 := proj2_sig (square_up_exists X2 claim2)).
    cbn beta in claim5, claim6.
    fold sup_X1 in claim5.
    fold sup_X2 in claim6.
    assert (claim7 : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
    { destruct (claim3 sup_X1) as [sup_X2_x1 [sup_f_X1_x2 [sup_X2_x1_isSupremum [sup_f_X1_x2_isSupremum Heq]]]].
      assert (isSupremum_iff_eq : isSupremum (f (sup_X1, sup_X2)) (image (fun x2 : D2 => f (sup_X1, x2)) X2) <-> sup_f_X1_x2 == f (sup_X1, sup_X2)) by now apply (isSupremum_unique (image (fun x2 : D2 => f (sup_X1, x2)) X2)).
      assert (sup_X2_x1_eq_sup_X2 := proj1 (isSupremum_unique X2 sup_X2_x1 sup_X2_x1_isSupremum sup_X2) claim6).
      apply isSupremum_iff_eq.
      transitivity (f (sup_X1, sup_X2_x1)).
      - symmetry...
      - apply f_preserves_eq.
        split...
    }
    assert ( claim8 :
      forall x2 : D2,
      member x2 X2 ->
      isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1)
    ).
    { intros x2 x2_in.
      destruct (claim4 x2) as [sup_X1' [sup_f_X1_x2' [isSupremum_sup_X1' [isSupremum_sup_f_X1_x2' Heq]]]].
      assert (isSupremum_iff_eq : isSupremum (f (sup_X1, x2)) (image (fun x1 : D1 => f (x1, x2)) X1) <-> sup_f_X1_x2' == f (sup_X1, x2)) by now apply (isSupremum_unique (image (fun x1 : D1 => f (x1, x2)) X1)).
      assert (sup_X1'_eq_sup_X1 := proj1 (isSupremum_unique X1 sup_X1' isSupremum_sup_X1' sup_X1) claim5).
      apply isSupremum_iff_eq.
      transitivity (f (sup_X1', x2)).
      - symmetry...
      - apply f_preserves_eq.
        split...
    }
    assert (claim9 : isSupremum (f (sup_X1, sup_X2)) (image_sup (image (fun x2 : D2 => image (fun x1 : D1 => f (x1, x2)) X1) X2))).
    { split.
      - intros le_y y' [ys [ys_in y'_isSupremum_of_ys]].
        apply in_image_iff in ys_in.
        destruct ys_in as [x2 [ys_is x2_in]].
        subst ys.
        assert (f_sup_X1_x2_le_f_sup_X1_sup_X2 : f (sup_X1, x2) =< f (sup_X1, sup_X2)) by now apply (ContinuousMap_isMonotonicMap (fun x2 : D2 => f (sup_X1, x2)) (f1_continuous sup_X1)), claim6.
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
          - apply (ContinuousMap_isMonotonicMap (fun x2 : D2 => f (x1_1, x2)) (f1_continuous x1_1))...
          - apply (ContinuousMap_isMonotonicMap (fun x1 : D1 => f (x1, x2_3)) (f2_continuous x2_3))...
        }
        transitivity (f (x1_3, x2_3))...
    }
    intros _sup_X1 _sup_X1_isSupremum _sup_X2 _sup_X2_isSupremum.
    assert (claim12 : f (sup_X1, sup_X2) == f (_sup_X1, _sup_X2)).
    { apply f_preserves_eq.
      split; simpl.
      - apply (isSupremum_unique X1)...
      - apply (isSupremum_unique X2)...
    }
    apply (proj2 (isSupremum_unique (image f X) (f (sup_X1, sup_X2)) claim11 (f (_sup_X1, _sup_X2))))...
  Qed.

  Lemma show_that_f_isContinuousMap_if_f1_isContinuousMap_and_f2_isContinuousMap {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) -> D3,
    (forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2))) ->
    (forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2))) ->
    isContinuousMap f.
  Proof with eauto with *.
    intros f f1_continuous f2_continuous.
    assert (f1_monotonic := fun x1 : D1 => ContinuousMap_isMonotonicMap (fun x2 : D2 => f (x1, x2)) (f1_continuous x1)).
    assert (f2_monotonic := fun x2 : D2 => ContinuousMap_isMonotonicMap (fun x1 : D1 => f (x1, x2)) (f2_continuous x2)).
    assert (f1_preserves_eq := fun x1 : D1 => MonotonicMap_preservesSetoid (fun x2 : D2 => f (x1, x2)) (f1_monotonic x1)).
    assert (f2_preserves_eq := fun x2 : D2 => MonotonicMap_preservesSetoid (fun x1 : D1 => f (x1, x2)) (f2_monotonic x2)).
    assert (f_preserves_eq : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> f p1 == f p2).
    { intros [x1_1 x2_1] [x1_2 x2_2] [Heq1 Heq2].
      simpl in *.
      transitivity (f (x1_1, x2_2))...
    }
    apply the_main_reason_for_introducing_ScottTopology...
    intros X X_isDirected.
    set (X1 := image fst X).
    set (X2 := image snd X).
    set (claim1 := proj1 (directed_subset_of_direct_product X X_isDirected)).
    set (claim2 := proj2 (directed_subset_of_direct_product X X_isDirected)).
    assert (mayday := square_up_of_direct_product X X_isDirected).
    fold claim1 claim2 in mayday.
    fold X1 in claim1, mayday.
    fold X2 in claim2, mayday.
    set (sup_X1 := proj1_sig (square_up_exists X1 claim1)).
    set (sup_X2 := proj1_sig (square_up_exists X2 claim2)).
    fold sup_X1 sup_X2 in mayday.
    assert (sup_X1_isSupremum := proj2_sig (square_up_exists X1 claim1)).
    assert (sup_X2_isSupremum := proj2_sig (square_up_exists X2 claim2)).
    cbn beta in sup_X1_isSupremum, sup_X2_isSupremum.
    fold sup_X1 in sup_X1_isSupremum.
    fold sup_X2 in sup_X2_isSupremum.
    assert (it_is_sufficient_to_show := f_sup_X1_sup_X2_isSupremum_f_X1_X2 f f1_continuous f2_continuous X X_isDirected sup_X1 sup_X1_isSupremum sup_X2 sup_X2_isSupremum)...
  Qed.

  Lemma separately_continuous_iff {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) -> D3,
    ((forall x1 : D1, isContinuousMap (fun x2 : D2 => f (x1, x2))) /\ (forall x2 : D2, isContinuousMap (fun x1 : D1 => f (x1, x2)))) <-> isContinuousMap f.
  Proof with eauto with *.
    intros f.
    split.
    - intros [f1_continuous f2_continuous].
      apply show_that_f_isContinuousMap_if_f1_isContinuousMap_and_f2_isContinuousMap...
    - intros f_continuous.
      split; [apply show_that_f1_isContinuousMap_if_f_isContinuousMap | apply show_that_f2_isContinuousMap_if_f_isContinuousMap]...
  Qed.

  Definition ScottApp_aux1 {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : ((D ~> D') * D) -> D' :=
    fun f_x : (D ~> D') * D =>
    proj1_sig (fst f_x) (snd f_x) 
  .

  Lemma ScottApp_aux1_isMontonicMap {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    isMonotonicMap (fun f_x : (D ~> D') * D => ScottApp_aux1 f_x).
  Proof with eauto with *.
    unfold ScottApp_aux1.
    intros [f1 x1] [f2 x2] [Hle_f Hle_x].
    simpl in *.
    assert (claim1 : isContinuousMap (proj1_sig f1)) by exact (proj2_sig f1).
    transitivity (proj1_sig f1 x2); [apply ContinuousMap_isMonotonicMap | apply Hle_f]...
  Qed.

  Lemma ScottApp_aux1_preserves_eq {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall f1 : D ~> D',
    forall f2 : D ~> D',
    forall x1 : D,
    forall x2 : D,
    f1 == f2 ->
    x1 == x2 ->
    ScottApp_aux1 (f1, x1) == ScottApp_aux1 (f2, x2).
  Proof with eauto with *.
    intros f1 f2 x1 x2 Heq_f Heq_x.
    simpl.
    transitivity (proj1_sig f1 x2).
    - apply Poset_asym; apply (ContinuousMap_isMonotonicMap (proj1_sig f1) (proj2_sig f1))...
    - apply Heq_f.
  Qed.

  Lemma ScottApp_aux1_isContinuousMap {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    isContinuousMap (fun p : (D ~> D') * D => ScottApp_aux1 p).
  Proof with eauto with *.
    apply show_that_f_isContinuousMap_if_f1_isContinuousMap_and_f2_isContinuousMap.
    - exact (fun f : D ~> D' => proj2_sig f).
    - intros x.
      assert (mayday : isMonotonicMap (fun f : D ~> D' => ScottApp_aux1 (f, x))) by now unfold ScottApp_aux1.
      apply the_main_reason_for_introducing_ScottTopology.
      + intros f1 f2 Heq_f.
        apply (ScottApp_aux1_preserves_eq f1 f2 x x Heq_f)...
      + intros fs fs_isDirected.
        set (Y := image (fun f_i : D ~> D' => ScottApp_aux1 (f_i, x)) fs).
        set (f := fun x0 : D => proj1_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x0) fs) (Supremum_of_squigs_is_well_defined fs fs_isDirected x0))).
        set (sup_fs := exist isContinuousMap f (Supremum_of_squigs_exists_if_it_is_directed fs fs_isDirected)).
        assert (claim1 : forall x0 : D, isSupremum (f x0) (image (fun f_i : D ~> D' => proj1_sig f_i x0) fs)) by apply (fun x0 : D => proj2_sig (square_up_exists (image (fun f_i : D ~> D' => proj1_sig f_i x0) fs) (Supremum_of_squigs_is_well_defined fs fs_isDirected x0))).
        assert (claim2 : isSupremum sup_fs fs).
        { intros f1.
          split.
          - intros sup_fs_le_f1 f2 f2_in x0.
            apply (claim1 x0)...
          - intros f1_is_an_upper_bound x0.
            apply (claim1 x0).
            intros y2 y2_in.
            apply in_image_iff in y2_in.
            destruct y2_in as [f2 [y2_is f2_in]].
            subst y2.
            apply f1_is_an_upper_bound...
        }
        assert (claim3 : isSupremum (ScottApp_aux1 (sup_fs, x)) Y).
        { intros y.
          split.
          - intros le_y y' y'_in.
            apply (claim1 x)...
          - intros y_is_an_upper_bound.
            apply (claim1 x)...
        }
        exists sup_fs, (ScottApp_aux1 (sup_fs, x))...
  Qed.

  Definition ScottApp {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} : ((D ~> D') * D) ~> D' :=
    exist isContinuousMap (fun f_x : (D ~> D') * D => ScottApp_aux1 f_x) (@ScottApp_aux1_isContinuousMap D D' D_isPoset D'_isPoset D_isCompletePartialOrder D'_isCompletePartialOrder)
  .

  Definition ScottAbs_aux1 {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} : ((D1 * D2) ~> D3) -> D1 -> D2 -> D3 :=
    fun f : (D1 * D2) ~> D3 =>
    fun x1 : D1 =>
    fun x2 : D2 =>
    proj1_sig f (x1, x2)
  .

  Definition ScottAbs_aux2 {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} : ((D1 * D2) ~> D3) -> D1 -> (D2 ~> D3) :=
    fun f : (D1 * D2) ~> D3 =>
    fun x1 : D1 =>
    exist isContinuousMap (ScottAbs_aux1 f x1) (show_that_f1_isContinuousMap_if_f_isContinuousMap (proj1_sig f) (proj2_sig f) x1)
  .

  Lemma image_ScottAbs_aux2_f_X1_eq_ScottAbs_aux2_f_sup_X1 {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) ~> D3,
    forall X1 : ensemble D1,
    isDirected X1 ->
    forall sup_X1 : D1,
    isSupremum sup_X1 X1 ->
    forall sup_Y : D2 ~> D3,
    isSupremum sup_Y (image (ScottAbs_aux2 f) X1) ->
    arrow_eqProp D2 D3 (@Poset_requiresSetoid D3 D3_isPoset) (proj1_sig (ScottAbs_aux2 f sup_X1)) (proj1_sig sup_Y).
  Proof with eauto with *.
    intros f.
    assert (f_monotonic : isMonotonicMap (proj1_sig f)) by apply ContinuousMap_isMonotonicMap, proj2_sig.
    assert (f_preserves_eq : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> proj1_sig f p1 == proj1_sig f p2) by now apply (MonotonicMap_preservesSetoid (proj1_sig f)).
    set (ScottAbs := fun x1 : D1 => exist isContinuousMap (fun x2 : D2 => proj1_sig (ScottAbs_aux2 f x1) x2) (show_that_f1_isContinuousMap_if_f_isContinuousMap (proj1_sig f) (proj2_sig f) x1)).
    assert ( mayday :
      forall x1_1 : D1,
      forall x1_2 : D1,
      x1_1 == x1_2 ->
      ScottAbs x1_1 == ScottAbs x1_2
    ).
    { intros x1_1 x1_2 Heq1 x2.
      apply (f_preserves_eq (x1_1, x2) (x1_2, x2)).
      split...
    }
    assert (ScottAbs_monotonic : isMonotonicMap ScottAbs).
    { intros x1_1 x1_2 Hle1 x2.
      unfold ScottAbs.
      simpl.
      apply f_monotonic.
      split...
    }
    intros X1 X1_isDirected sup_X1 sup_X1_isSupremum sup_Y sup_Y_isSupremum.
    assert ( claim1 :
      forall x1 : D1,
      member x1 X1 ->
      forall x2 : D2,
      proj1_sig f (x1, x2) =< proj1_sig f (sup_X1, x2)
    ).
    { intros x1 x1_in x2.
      apply f_monotonic.
      split; simpl...
    }
    intros x2.
    assert (claim2 := f_sup_X1_x2_eq_sup_f_X1_x2 (proj1_sig f) (proj2_sig f) x2 X1 X1_isDirected sup_X1 sup_X1_isSupremum).
    apply Poset_asym.
    - apply claim2.
      intros y y_in.
      apply in_image_iff in y_in.
      destruct y_in as [x1 [y_is x1_in]].
      subst y.
      set (f1 := fun x : D2 => proj1_sig f (x1, x)).
      assert (f1_continuous : isContinuousMap f1) by now apply (show_that_f1_isContinuousMap_if_f_isContinuousMap (proj1_sig f) (proj2_sig f)).
      assert (claim3 : exist isContinuousMap f1 f1_continuous =< sup_Y).
      { apply sup_Y_isSupremum.
        - reflexivity.
        - apply in_image_iff.
          exists x1.
          split.
          + rewrite (proof_irrelevance (isContinuousMap (fun x : D2 => proj1_sig f (x1, x))) f1_continuous (show_that_f1_isContinuousMap_if_f_isContinuousMap (proj1_sig f) (proj2_sig f) x1))...
          + apply x1_in.
      }
      apply claim3.
    - transitivity (proj1_sig f (sup_X1, x2)).
      + set (f1 := fun x : D2 => proj1_sig f (sup_X1, x)).
        assert (f1_continuous : isContinuousMap f1) by now apply (show_that_f1_isContinuousMap_if_f_isContinuousMap (proj1_sig f) (proj2_sig f)).
        enough (claim4 : sup_Y =< exist isContinuousMap f1 f1_continuous) by apply claim4.
        apply sup_Y_isSupremum.
        intros f_i f_i_in.
        apply in_image_iff in f_i_in.
        destruct f_i_in as [x1 [f_i_is x1_in]].
        subst f_i.
        exact (claim1 x1 x1_in).
      + apply claim2.
        intros y y_in.
        apply in_image_iff in y_in.
        destruct y_in as [x1 [y_is x1_in]].
        subst y...
  Qed.

  Lemma ScottAbs_aux2_isContinuousMap {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    forall f : (D1 * D2) ~> D3,
    isContinuousMap (fun x1 : D1 => exist isContinuousMap (fun x2 : D2 => proj1_sig (ScottAbs_aux2 f x1) x2) (show_that_f1_isContinuousMap_if_f_isContinuousMap (proj1_sig f) (proj2_sig f) x1)).
  Proof with eauto with *.
    intros f.
    assert (f_monotonic : isMonotonicMap (proj1_sig f)) by apply ContinuousMap_isMonotonicMap, proj2_sig.
    assert (f_preserves_eq : forall p1 : D1 * D2, forall p2 : D1 * D2, p1 == p2 -> proj1_sig f p1 == proj1_sig f p2) by now apply (MonotonicMap_preservesSetoid (proj1_sig f)).
    set (ScottAbs := fun x1 : D1 => exist isContinuousMap (fun x2 : D2 => proj1_sig (ScottAbs_aux2 f x1) x2) (show_that_f1_isContinuousMap_if_f_isContinuousMap (proj1_sig f) (proj2_sig f) x1)).
    assert ( mayday :
      forall x1_1 : D1,
      forall x1_2 : D1,
      x1_1 == x1_2 ->
      ScottAbs x1_1 == ScottAbs x1_2
    ).
    { intros x1_1 x1_2 Heq1 x2.
      apply (f_preserves_eq (x1_1, x2) (x1_2, x2)).
      split...
    }
    assert (ScottAbs_monotonic : isMonotonicMap ScottAbs).
    { intros x1_1 x1_2 Hle1 x2.
      apply f_monotonic.
      split...
    }
    apply the_main_reason_for_introducing_ScottTopology...
    intros X1 X1_isDirected.
    assert (image_ScottAbs_X1_isDirected : isDirected (image ScottAbs X1)) by now apply MonotonicMap_preservesDirected.
    destruct (square_up_exists X1 X1_isDirected) as [sup_X1 sup_X1_isSupremum].
    set (sup_Y := square_up_of_squigs (image ScottAbs X1) image_ScottAbs_X1_isDirected).
    assert (sup_Y_isSupremum := square_up_of_squigs_isSupremum (image ScottAbs X1) image_ScottAbs_X1_isDirected).
    assert (it_is_sufficient_to_show := image_ScottAbs_aux2_f_X1_eq_ScottAbs_aux2_f_sup_X1 f X1 X1_isDirected sup_X1 sup_X1_isSupremum sup_Y sup_Y_isSupremum)...
  Qed.

  Definition ScottAbs_aux3 {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} : ((D1 * D2) ~> D3) -> (D1 ~> (D2 ~> D3)) :=
    fun f : (D1 * D2) ~> D3 =>
    exist isContinuousMap (ScottAbs_aux2 f) (ScottAbs_aux2_isContinuousMap f)
  .

  Definition ScottAbs_aux3_isMonotonicMap {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} : isMonotonicMap (fun f : (D1 * D2) ~> D3 => ScottAbs_aux3 f) :=
    fun f1 : (D1 * D2) ~> D3 =>
    fun f2 : (D1 * D2) ~> D3 =>
    fun Hle_f : f1 =< f2 =>
    fun x1 : D1 =>
    fun x2 : D2 =>
    Hle_f (x1, x2)
  .

  Lemma ScottAbs_aux3_isContinuousMap {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} :
    isContinuousMap (fun f : (D1 * D2) ~> D3 => ScottAbs_aux3 f).
  Proof with eauto with *.
    assert (ScottAbs_aux3_monotonic : isMonotonicMap (fun f : (D1 * D2) ~> D3 => ScottAbs_aux3 f)) by exact ScottAbs_aux3_isMonotonicMap.
    assert (ScottAbs_aux3_preserves_eq : forall f1 : (D1 * D2) ~> D3, forall f2 : (D1 * D2) ~> D3, f1 == f2 -> ScottAbs_aux3 f1 == ScottAbs_aux3 f2) by now apply MonotonicMap_preservesSetoid.
    apply the_main_reason_for_introducing_ScottTopology...
    intros F F_isDirected.
    set (sup_F := square_up_of_squigs F F_isDirected).
    assert (sup_F_isSupremum := square_up_isSupremum F F_isDirected).
    assert (claim1 := image_ScottAbs_aux2_f_X1_eq_ScottAbs_aux2_f_sup_X1 sup_F).
    assert (claim2 : forall p : D1 * D2, isSupremum (proj1_sig (proj1_sig (ScottAbs_aux3 sup_F) (fst p)) (snd p)) (image (fun f_i : (D1 * D2) ~> D3 => proj1_sig f_i p) F)).
    { intros [x1 x2].
      exact (proj2_sig (square_up_exists (image (fun f_i : (D1 * D2) ~> D3 => proj1_sig f_i (x1, x2)) F) (Supremum_of_squigs_is_well_defined F F_isDirected (x1, x2)))).
    }
    set (sup_G := fun p : D1 * D2 => proj1_sig (proj1_sig (ScottAbs_aux3 sup_F) (fst p)) (snd p)).
    assert (claim3 : @eqProp ((D1 * D2) -> D3) (@Poset_requiresSetoid ((D1 * D2) -> D3) (@arrow_isPoset (D1 * D2) D3 D3_isPoset)) sup_G (proj1_sig sup_F)).
    { intros [x1 x2].
      reflexivity.
    }
    assert (claim4 : @isSupremum ((D1 * D2) -> D3) (@arrow_isPoset (D1 * D2) D3 D3_isPoset) sup_G (image (fun f_i : (D1 * D2) ~> D3 => proj1_sig f_i) F)).
    { intros g1.
      split.
      - intros sup_G_le_g1 g2 g2_in.
        apply in_image_iff in g2_in.
        destruct g2_in as [f_i [g2_is f_i_in]].
        subst g2.
        apply (Poset_trans (proj1_sig f_i) sup_G g1).
        + apply (Poset_trans (proj1_sig f_i) (proj1_sig sup_F) sup_G).
          * apply sup_F_isSupremum...
          * exact (Poset_refl2 sup_G (proj1_sig sup_F) claim3).
        + exact sup_G_le_g1.
      - intros g1_is_an_upper_bound [x1 x2].
        apply claim2.
        intros y y_in.
        apply in_image_iff in y_in.
        destruct y_in as [f_i [y_is f_i_in]].
        subst y.
        apply (g1_is_an_upper_bound (proj1_sig f_i))...
    }
    enough (it_is_sufficient_to_show : isSupremum (ScottAbs_aux3 sup_F) (image (fun f_i : (D1 * D2) ~> D3 => ScottAbs_aux3 f_i) F)) by now exists sup_F, (ScottAbs_aux3 sup_F).
    intros h.
    split.
    - intros le_h h0 h0_in.
      apply in_image_iff in h0_in.
      destruct h0_in as [f_i [h0_is f_i_in]].
      subst h0.
      transitivity (ScottAbs_aux3 sup_F).
      + apply ScottAbs_aux3_monotonic, sup_F_isSupremum...
      + apply le_h.
    - intros h_is_an_upper_bound.
      assert ( claim5 :
        forall g : (D1 * D2) -> D3,
        member g (image (fun f_i : (D1 * D2) ~> D3 => proj1_sig f_i) F) ->
        @leProp ((D1 * D2) -> D3) (@arrow_isPoset (D1 * D2) D3 D3_isPoset) g (fun p : D1 * D2 => proj1_sig (proj1_sig h (fst p)) (snd p))
      ).
      { intros g g_in.
        apply in_image_iff in g_in.
        destruct g_in as [f_i [g_is f_i_in]].
        subst g.
        intros [x1 x2].
        apply (h_is_an_upper_bound (ScottAbs_aux3 f_i))...
      }
      assert (claim6 : @leProp ((D1 * D2) -> D3) (@arrow_isPoset (D1 * D2) D3 D3_isPoset) sup_G (fun p : D1 * D2 => proj1_sig (proj1_sig h (fst p)) (snd p))) by now apply claim4.
      intros x1 x2.
      transitivity (sup_G (x1, x2)).
      + apply Poset_refl2...
      + apply claim6...
  Qed.

  Definition ScottAbs {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} `{D1_isCompletePartialOrder : @isCompletePartialOrder D1 D1_isPoset} `{D2_isCompletePartialOrder : @isCompletePartialOrder D2 D2_isPoset} `{D3_isCompletePartialOrder : @isCompletePartialOrder D3 D3_isPoset} : ((D1 * D2) ~> D3) ~> (D1 ~> (D2 ~> D3)) :=
    exist isContinuousMap (fun f : (D1 * D2) ~> D3 => ScottAbs_aux3 f) (@ScottAbs_aux3_isContinuousMap D1 D2 D3 D1_isPoset D2_isPoset D3_isPoset D1_isCompletePartialOrder D2_isCompletePartialOrder D3_isCompletePartialOrder)
  .

  Definition iteration {D : Type} : nat -> (D -> D) -> D -> D :=
    fix iteration_fix (n : nat) {struct n} : (D -> D) -> D -> D :=
    match n return (D -> D) -> (D -> D) with
    | O =>
      fun f : D -> D =>
      fun x : D =>
      x
    | S n' =>
      fun f : D -> D =>
      fun x : D =>
      f (iteration_fix n' f x)
    end
  .

  Inductive iterations {D : Type} (f : D -> D) (x : D) : ensemble D :=
  | in_iterations :
    forall n : nat,
    member (iteration n f x) (iterations f x)
  .

  Local Hint Constructors iterations : core.

  Lemma iterations_f_bottom_isDirected_if_f_isContinuousMap {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} :
    forall f : D -> D,
    isContinuousMap f ->
    isDirected (iterations f (proj1_sig bottom_exists)).
  Proof with eauto with *.
    assert (claim1 := n1_le_max_n1_n2).
    assert (claim2 := n2_le_max_n1_n2).
    intros f f_continuous.
    assert (claim3 : forall n : nat, iteration n f (proj1_sig bottom_exists) =< iteration (S n) f (proj1_sig bottom_exists)).
    { induction n as [| n' IH].
      - exact (proj2_sig bottom_exists (f (proj1_sig bottom_exists))).
      - exact (ContinuousMap_isMonotonicMap f f_continuous (iteration n' f (proj1_sig bottom_exists)) (iteration (S n') f (proj1_sig bottom_exists)) IH).
    }
    assert (claim4 : forall n1 : nat, forall n2 : nat, n1 <= n2 -> iteration n1 f (proj1_sig bottom_exists) =< iteration n2 f (proj1_sig bottom_exists)).
    { intros n1 n2 n1_le_n2.
      induction n1_le_n2 as [| n2 n1_le_n2 IH].
      - reflexivity.
      - transitivity (iteration n2 f (proj1_sig bottom_exists))...  
    }
    split.
    - exists (iteration O f (proj1_sig bottom_exists))...
    - intros x1 x1_in x2 x2_in.
      inversion x1_in; subst.
      rename n into n1.
      inversion x2_in; subst.
      rename n into n2.
      exists (iteration (max n1 n2) f (proj1_sig bottom_exists))...
  Qed.

  Definition get_lfp_of {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} : (D ~> D) -> D :=
    fun f : D ~> D =>
    proj1_sig (square_up_exists (iterations (proj1_sig f) (proj1_sig bottom_exists)) (iterations_f_bottom_isDirected_if_f_isContinuousMap (proj1_sig f) (proj2_sig f)))
  .

  Lemma every_ContinuousMap_has_a_fixed_point {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} :
    forall f : D ~> D,
    member (get_lfp_of f) (fixed_points (proj1_sig f)).
  Proof with eauto with *.
    intros f.
    assert (claim1 : isSupremum (get_lfp_of f) (iterations (proj1_sig f) (proj1_sig bottom_exists))) by exact (proj2_sig (square_up_exists (iterations (proj1_sig f) (proj1_sig bottom_exists)) (iterations_f_bottom_isDirected_if_f_isContinuousMap (proj1_sig f) (proj2_sig f)))).
    assert (claim2 : forall n : nat, iteration n (proj1_sig f) (proj1_sig bottom_exists) =< iteration (S n) (proj1_sig f) (proj1_sig bottom_exists)).
    { induction n as [| n' IH].
      - exact (proj2_sig bottom_exists (proj1_sig f (proj1_sig bottom_exists))).
      - exact (ContinuousMap_isMonotonicMap (proj1_sig f) (proj2_sig f) (iteration n' (proj1_sig f) (proj1_sig bottom_exists)) (iteration (S n') (proj1_sig f) (proj1_sig bottom_exists)) IH).
    }
    assert (claim3 := isSupremum_of_image_f_X_iff_f_sup_X_eq (proj1_sig f) (proj2_sig f) (iterations (proj1_sig f) (proj1_sig bottom_exists)) (iterations_f_bottom_isDirected_if_f_isContinuousMap (proj1_sig f) (proj2_sig f)) (get_lfp_of f) claim1).
    assert (it_is_sufficient_to_show : proj1_sig f (get_lfp_of f) == get_lfp_of f).
    { apply claim3.
      intros y.
      split.
      - intros le_y y0 y0_in.
        apply in_image_iff in y0_in.
        destruct y0_in as [x0 [y0_is x0_in]].
        subst y0.
        inversion x0_in; subst.
        replace (proj1_sig f (iteration n (proj1_sig f) (proj1_sig bottom_exists))) with (iteration (S n) (proj1_sig f) (proj1_sig bottom_exists))...
      - intros y_is_an_upper_bound.
        apply claim1.
        intros y0 y0_in.
        inversion y0_in; subst.
        destruct n as [| n']; simpl.
        + apply (proj2_sig bottom_exists).
        + apply y_is_an_upper_bound...
    }
    exact (Setoid_sym (proj1_sig f (get_lfp_of f)) (get_lfp_of f) it_is_sufficient_to_show).
  Qed.

  Lemma get_lfp_of_f_returns_the_least_fixed_point_of_f {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} :
    forall f : D ~> D,
    isLeastFixedPoint (get_lfp_of f) (proj1_sig f).
  Proof with eauto with *.
    intros f.
    assert (claim1 : isSupremum (get_lfp_of f) (iterations (proj1_sig f) (proj1_sig bottom_exists))) by exact (proj2_sig (square_up_exists (iterations (proj1_sig f) (proj1_sig bottom_exists)) (iterations_f_bottom_isDirected_if_f_isContinuousMap (proj1_sig f) (proj2_sig f)))).
    assert (claim2 : forall n : nat, iteration n (proj1_sig f) (proj1_sig bottom_exists) =< iteration (S n) (proj1_sig f) (proj1_sig bottom_exists)).
    { induction n as [| n IH].
      - exact (proj2_sig bottom_exists (proj1_sig f (proj1_sig bottom_exists))).
      - exact (ContinuousMap_isMonotonicMap (proj1_sig f) (proj2_sig f) (iteration n (proj1_sig f) (proj1_sig bottom_exists)) (iteration (S n) (proj1_sig f) (proj1_sig bottom_exists)) IH).
    }
    assert (claim3 := every_ContinuousMap_has_a_fixed_point f).
    assert (claim4 := ContinuousMap_isMonotonicMap (proj1_sig f) (proj2_sig f)).
    enough (it_is_sufficient_to_show : forall y : D, y == proj1_sig f y -> get_lfp_of f =< y) by now split.
    intros y y_is_fixpoint_of_f.
    assert (claim5 : forall n : nat, iteration n (proj1_sig f) (proj1_sig bottom_exists) =< y).
    { induction n as [| n' IH]; simpl.
      - apply (proj2_sig bottom_exists).
      - transitivity (proj1_sig f y)...
    }
    apply claim1.
    intros x x_in.
    inversion x_in; subst...
  Qed.

  Lemma f_mapsto_iteration_n_f_bottom_isContinuousMap_for_any_n {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} :
    forall n : nat,
    isContinuousMap (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)).
  Proof with eauto with *.
    assert (iteration_isMonotonicMap : forall n : nat, isMonotonicMap (fun p : (D ~> D) * D => iteration n (proj1_sig (fst p)) (snd p))).
    { induction n as [| n IH]; intros [f1 x1] [f2 x2] [Hle_f Hle_x]; simpl.
      - exact Hle_x.
      - transitivity (proj1_sig f2 (iteration n (proj1_sig f1) x1)).
        + apply Hle_f.
        + apply (ContinuousMap_isMonotonicMap (proj1_sig f2) (proj2_sig f2)).
          apply (IH (f1, x1) (f2, x2)).
          split...
    }
    assert (claim1 : forall n : nat, isMonotonicMap (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists))).
    { intros n f1 f2 f1_le_f2.
      apply (iteration_isMonotonicMap n (f1, proj1_sig bottom_exists) (f2, proj1_sig bottom_exists)).
      split...
    }
    induction n as [| n IH].
    - apply bot_of_squigs_isContinuousMap.
    - apply the_main_reason_for_introducing_ScottTopology.
      + apply MonotonicMap_preservesSetoid...
      + intros F F_isDirected.
        set (sup_F := square_up_of_squigs F F_isDirected).
        assert (sup_F_isSupremum : isSupremum sup_F F) by now apply square_up_of_squigs_isSupremum.
        set (Y := image (fun f : D ~> D => iteration (S n) (proj1_sig f) (proj1_sig bottom_exists)) F).
        assert (Y_isDirected : isDirected Y) by now apply MonotonicMap_preservesDirected.
        set (X := image (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)) F).
        assert (X_isDirected : isDirected X).
        { apply MonotonicMap_preservesDirected.
          - apply ContinuousMap_isMonotonicMap.
            exact IH.
          - exact F_isDirected.
        }
        set (sup_X := iteration n (proj1_sig sup_F) (proj1_sig bottom_exists)).
        assert (sup_X_isSupremum : isSupremum sup_X X) by exact (ContinuousMapsOnCpos_preservesSupremum (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)) IH F F_isDirected sup_F sup_F_isSupremum).
        set (sup_Y := proj1_sig sup_F (iteration n (proj1_sig sup_F) (proj1_sig bottom_exists))).
        assert (sup_F_sup_X_eq_sup_Y : proj1_sig sup_F sup_X == sup_Y).
        { apply MonotonicMap_preservesSetoid.
          - exact (ContinuousMap_isMonotonicMap (proj1_sig sup_F) (proj2_sig sup_F)).
          - symmetry...
        }
        assert (sup_X_eq_iteration_n_sup_F_bot : iteration n (proj1_sig sup_F) (proj1_sig bottom_exists) == sup_X) by exact (proj1 (isSupremum_of_image_f_X_iff_f_sup_X_eq (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)) IH F F_isDirected sup_F sup_F_isSupremum sup_X) sup_X_isSupremum).
        assert (sup_F_sup_X_isSupremum : isSupremum (proj1_sig sup_F sup_X) (unions (image (fun f_i : D ~> D => image (fun x : D => proj1_sig f_i x) X) F))) by exact (Supremum_of_squigs_sup_X_isSupremum_unions_i_image_f_i_X_F F F_isDirected X X_isDirected sup_X sup_X_isSupremum).
        enough (it_is_sufficient_to_show : isSupremum sup_Y Y) by now simpl; exists sup_F, sup_Y.
        intros y.
        split.
        { intros le_y y0 y0_in.
          apply in_image_iff in y0_in.
          destruct y0_in as [f_i [y0_is f_i_in]].
          subst y0.
          transitivity (proj1_sig f_i sup_X).
          - simpl.
            apply (ContinuousMap_isMonotonicMap (proj1_sig f_i) (proj2_sig f_i)).
            apply sup_X_isSupremum...
          - transitivity (proj1_sig sup_F sup_X).
            + apply sup_F_isSupremum...
            + transitivity sup_Y...
        }
        { intros y_is_an_upper_bound.
          transitivity (proj1_sig sup_F sup_X).
          - apply Poset_refl2...
          - apply sup_F_sup_X_isSupremum.
            intros y0 y0_in.
            apply in_unions_iff in y0_in.
            destruct y0_in as [ys [y0_in ys_in]].
            apply in_image_iff in ys_in.
            destruct ys_in as [f1 [ys_is f1_in]].
            subst ys.
            apply in_image_iff in y0_in.
            destruct y0_in as [x [y0_is x_in_X]].
            subst y0.
            apply in_image_iff in x_in_X.
            destruct x_in_X as [f2 [x_is f2_in]].
            subst x.
            destruct (proj2 F_isDirected f1 f1_in f2 f2_in) as [f3 [f3_in [f1_le_f3 f2_le_f3]]].
            assert (so_we_obtain : proj1_sig f1 (iteration n (proj1_sig f2) (proj1_sig bottom_exists)) =< proj1_sig f3 (iteration n (proj1_sig f3) (proj1_sig bottom_exists))).
            { transitivity (proj1_sig f3 (iteration n (proj1_sig f2) (proj1_sig bottom_exists))).
              - apply f1_le_f3.
              - apply (ContinuousMap_isMonotonicMap (proj1_sig f3) (proj2_sig f3)).
                apply claim1...
            }
            transitivity (proj1_sig f3 (iteration n (proj1_sig f3) (proj1_sig bottom_exists)))...
        }
  Qed.

  Lemma get_lfp_of_isContinuousMap {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} :
    isContinuousMap (fun f : D ~> D => get_lfp_of f).
  Proof with eauto with *.
    assert (get_lfp_of_isSupremum_of_iterations : forall f : D ~> D, isSupremum (get_lfp_of f) (iterations (proj1_sig f) (proj1_sig bottom_exists))) by exact (fun f : D ~> D => proj2_sig (square_up_exists (iterations (proj1_sig f) (proj1_sig bottom_exists)) (iterations_f_bottom_isDirected_if_f_isContinuousMap (proj1_sig f) (proj2_sig f)))).
    assert (iteration_isMonotonicMap : forall n : nat, isMonotonicMap (fun p : (D ~> D) * D => iteration n (proj1_sig (fst p)) (snd p))).
    { induction n as [| n IH]; intros [f1 x1] [f2 x2] [Hle_f Hle_x]; simpl.
      - exact Hle_x.
      - transitivity (proj1_sig f2 (iteration n (proj1_sig f1) x1)).
        + apply Hle_f.
        + apply (ContinuousMap_isMonotonicMap (proj1_sig f2) (proj2_sig f2)).
          apply (IH (f1, x1) (f2, x2)).
          split...
    }
    assert (get_lfp_of_isMonotonicMap : isMonotonicMap (fun f : D ~> D => get_lfp_of f)).
    { intros f1 f2 f1_le_f2.
      apply (get_lfp_of_isSupremum_of_iterations f1).
      intros y y_in.
      inversion y_in; subst.
      transitivity (iteration n (proj1_sig f2) (proj1_sig bottom_exists)).
      - apply (iteration_isMonotonicMap n (f1, proj1_sig bottom_exists) (f2, proj1_sig bottom_exists)).
        split...
      - apply (get_lfp_of_isSupremum_of_iterations f2)...
    }
    intros O O_isOpen.
    assert (claim1 : forall n : nat, isOpen (preimage (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)) O)) by exact (fun n : nat => f_mapsto_iteration_n_f_bottom_isContinuousMap_for_any_n n O O_isOpen).
    assert (claim2 : isOpen (unions (fun F : ensemble (D ~> D) => exists n : nat, F == preimage (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)) O))).
    { apply open_unions.
      intros F [n F_eq].
      apply (open_ext_eq (preimage (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)) O) (claim1 n)).
      exact (Setoid_sym F (preimage (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)) O) F_eq).
    }
    apply (open_ext_eq (unions (fun F : ensemble (D ~> D) => exists n : nat, F == preimage (fun f : D ~> D => iteration n (proj1_sig f) (proj1_sig bottom_exists)) O)) claim2).
    intros f.
    split.
    - intros f_in.
      apply in_unions_iff in f_in.
      destruct f_in as [F [f_in_F [n F_eq]]].
      apply (in_preimage_iff f).
      assert (f_in : member f (preimage (fun f_i : D ~> D => iteration n (proj1_sig f_i) (proj1_sig bottom_exists)) O)) by now apply F_eq.
      apply (in_preimage_iff f) in f_in.
      apply (proj1 O_isOpen (iteration n (proj1_sig f) (proj1_sig bottom_exists)) (get_lfp_of f) f_in)...
    - intros f_in.
      apply (in_preimage_iff f) in f_in.
      destruct (proj2 O_isOpen (iterations (proj1_sig f) (proj1_sig bottom_exists)) (iterations_f_bottom_isDirected_if_f_isContinuousMap (proj1_sig f) (proj2_sig f)) (get_lfp_of f) (get_lfp_of_isSupremum_of_iterations f) f_in) as [f_i f_i_in].
      apply in_intersection_iff in f_i_in.
      destruct f_i_in as [f_i_in_iterations f_i_in_O].
      inversion f_i_in_iterations; subst.
      exists (preimage (fun f_i : D ~> D => iteration n (proj1_sig f_i) (proj1_sig bottom_exists)) O)...
  Qed.

  Definition getLeastFixedPointOf {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} : (D ~> D) ~> D :=
    exist isContinuousMap (@get_lfp_of D D_isPoset D_isCompletePartialOrder) (@get_lfp_of_isContinuousMap D D_isPoset D_isCompletePartialOrder)
  .

End ClassicalCpoTheory.
