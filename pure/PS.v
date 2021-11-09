Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.pure.MyUtilities.

Module ProblemSolving.

  Section Problem1.

  Import ListNotations MyUtilities.

  Fixpoint count_true (bs : list bool) : nat :=
    match bs with
    | [] => 0
    | b :: bs' => if b then S (count_true bs') else count_true bs'
    end
  .

  Fixpoint count_false (bs : list bool) : nat :=
    match bs with
    | [] => 0
    | b :: bs' => if b then count_false bs' else S (count_false bs')
    end
  .

  Definition L (bs : list bool) : Prop :=
    count_true bs = count_false bs
  .

  Inductive G : list bool -> Prop :=
  | G1 : G []
  | G2 : forall bs1, G bs1 -> G ([true] ++ bs1 ++ [false])
  | G3 : forall bs1, G bs1 -> G ([false] ++ bs1 ++ [true])
  | G4 : forall bs1 bs2, G bs1 -> G bs2 -> G (bs1 ++ bs2)
  .

  Local Hint Constructors G : core.

  Fixpoint movePiece (piece_pos : nat * nat) (bs : list bool) : (nat * nat) :=
    match bs with
    | [] => piece_pos
    | b :: bs' =>
      let x : nat := fst piece_pos in
      let y : nat := snd piece_pos in
      movePiece (if b then S x else x, if b then y else S y) bs'
    end
  .

(*

  Fixpoint drop {A : Type} (n : nat) (xs : list A) : list A :=
    match n with
    | 0 => xs
    | S n' => drop n' (tail xs)
    end
  .

  Lemma over_drop_is_nil {A : Type} :
    forall xs : list A,
    forall n : nat,
    length xs <= n ->
    drop n xs = [].
  Proof with (lia || eauto).
    induction xs as [| x xs IH]; simpl...
    - intros n H_le.
      induction n as [| n IHn]; simpl.
      + reflexivity.
      + rewrite IHn...
    - intros n H_le.
      inversion H_le; subst...
      apply IH...
  Qed.

  Lemma good_drop_is_suffix {A : Type} :
    forall n : nat,
    forall xs : list A,
    n <= length xs ->
    exists prefix_of_xs : list A, length prefix_of_xs = n /\ xs = prefix_of_xs ++ drop n xs.
  Proof with eauto.
    induction n as [| n IH].
    - intros xs H_le; simpl.
      exists []...
    - intros xs H_le; simpl.
      destruct xs as [| x xs].
      + inversion H_le.
      + apply (le_elim_S_n_le_m n (S (length xs))) in H_le.
        simpl in *.
        destruct (IH xs H_le) as [prefix_of_xs [H_length H_prefix]].
        exists (x :: prefix_of_xs); simpl.
        split...
        now rewrite <- H_prefix.
  Qed.

  Fixpoint enum_le (n : nat) : list nat :=
    match n with
    | 0 => n :: []
    | S n' => n :: enum_le n'
    end
  .

  Lemma in_enum_le_iff :
    forall n : nat,
    forall i : nat,
    i <= n <-> In i (enum_le n).
  Proof with (lia || eauto).
    intros n i.
    split.
    - intros H_le.
      induction H_le as [| n H_le IH]; simpl...
      induction i as [| i IH]; simpl...
    - induction n as [| n IH]; simpl...
      intros [H1 | H2]...
  Qed.

  Definition collect_points (bs : list bool) : list nat :=
    filter (fun i => count_true (drop i bs) =? count_false (drop i bs)) (enum_le (length bs))
  .

  Theorem completeness :
    forall bs : list bool,
    L bs ->
    G bs.
  Proof with eauto.
    assert (aux_lemma1 : forall xs : list nat, forall y : nat, forall z : nat, y <> z -> In y xs -> In z xs -> length xs >= 2).
    { induction xs as [| x1 [| x2 xs] IH]; simpl...
      - tauto.
      - intros y z H [H0 | []] [H1 | []].
        subst y z.
        contradiction.
      - lia.
    }
    assert (aux_lemma2 : forall property : list bool -> Prop, forall acc_claim : forall bs1 : list bool, (forall bs2 : list bool, length bs2 < length bs1 -> property bs2) -> property bs1, forall bs : list bool, property bs).
    { intros property acc_claim bs.
      apply acc_claim.
      induction bs as [| b bs IH]; simpl.
      - lia.
      - intros bs1 H_lt1.
        apply acc_claim.
        intros bs2 H_lt2.
        apply IH.
        lia.
    }
    assert (length_bs_in_collect_points_bs : forall bs : list bool, In (length bs) (collect_points bs)).
    { unfold collect_points.
      intros bs.
      apply filter_In.
      split.
      - apply in_enum_le_iff...
      - apply Nat.eqb_eq.
        replace (drop (length bs) bs) with (@nil bool).
        + reflexivity.
        + symmetry.
          apply over_drop_is_nil with (xs := bs) (n := length bs)...
    }
    assert (L_iff : forall bs : list bool, L bs <-> In 0 (collect_points bs)).
    { intros bs.
      unfold L, collect_points.
      rewrite filter_In.
      simpl.
      rewrite Nat.eqb_eq.
      rewrite <- (in_enum_le_iff (length bs) 0).
      lia.
    }
    assert ( L_implies_collect_points_bs_not_nil :
      forall bs : list bool,
      L bs ->
      length (collect_points bs) >= 1
    ).
    { intros bs L_bs.
      assert (H := proj1 (L_iff bs) L_bs).
      destruct (collect_points bs); [contradiction H | simpl; lia].
    }
    set (rank := fun bs : list bool => length (collect_points bs)).
    enough (it_is_sufficient_to_show : forall n : nat, forall bs : list bool, S n = rank bs -> L bs -> G bs).
    { intros bs L_bs.
      assert (rank_bs_ge_1 : rank bs >= 1) by now apply L_implies_collect_points_bs_not_nil with (bs := bs).
      assert (n_exists : exists n : nat, S n = rank bs).
      { exists (pred (rank bs)).
        pose (guarantee1_S_pred_n_eq_n rank_bs_ge_1)...
      }
      destruct n_exists as [n rank_bs_eq_S_n].
      apply it_is_sufficient_to_show with (n := n) (bs := bs)...
    }
    induction n as [| [| n] IH].
    { intros bs rank_bs_eq_1 L_bs.
      enough (in_this_case_bs_is_nil : bs = []) by now rewrite in_this_case_bs_is_nil.
      unfold rank in rank_bs_eq_1.
      destruct bs as [| b bs].
      - reflexivity.
      - assert (H_in_1 := proj1 (L_iff (b :: bs)) L_bs).
        assert (H_in_2 := length_bs_in_collect_points_bs (b :: bs)).
        set (my_bs := collect_points (b :: bs)).
        fold my_bs in rank_bs_eq_1, H_in_1, H_in_2.
        simpl in H_in_2.
        assert (H_trivial : 0 <> S (length bs)) by lia.
        enough (H_length : length my_bs >= 2) by lia...
    }
    all: intros bs; pattern bs; revert bs; apply aux_lemma2.
    { intros bs acc_hyp H_rank_bs_is_2 L_bs.
      enough (in_this_case_bs_is_1_bs'_0_or_0_bs'_1 : exists bs' : list bool, (2 = rank bs' /\ L bs') /\ (bs = [true] ++ bs' ++ [false] \/ bs = [false] ++ bs' ++ [true])).
      { destruct in_this_case_bs_is_1_bs'_0_or_0_bs'_1 as [bs' [[H_rank_bs'_is_2 L_bs'] [H_bs_is | H_bs_is]]].
        - rewrite H_bs_is.
          apply G2, acc_hyp...
          rewrite H_bs_is.
          repeat (rewrite app_length).
          simpl.
          lia.
        - rewrite H_bs_is.
          apply G3, acc_hyp...
          rewrite H_bs_is.
          repeat (rewrite app_length).
          simpl.
          lia.
      }
      
    }
    { 
    }
  Qed.

*)

  End Problem1.

End ProblemSolving.
