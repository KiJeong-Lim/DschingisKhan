Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module BinTree.

  Import ListNotations EqFacts MyUtilities BasicSetoidTheory BasicPosetTheory.

  Section INDICES_OF_BINARY_TREES.

  Inductive dir_t : Set :=
  | Dir_left : dir_t
  | Dir_right : dir_t
  .

  Definition dir_compare (d1 : dir_t) (d2 : dir_t) : comparison :=
    match d1, d2 with
    | Dir_left, Dir_left => Eq
    | Dir_left, Dir_right => Lt
    | Dir_right, Dir_left => Gt
    | Dir_right, Dir_right => Eq
    end
  .

  Global Program Instance dir_isPoset : isPoset dir_t :=
    { leProp :=
      fun d1 : dir_t =>
      fun d2 : dir_t =>
      dir_compare d1 d2 = Lt \/ dir_compare d1 d2 = Eq
    ; Poset_requiresSetoid :=
      {| eqProp := @eq dir_t; Setoid_requiresEquivalence := eq_equivalence |}
    }
  .

  Next Obligation with eauto with *.
    split.
    - intros [ | ]...
    - intros [ | ] [ | ] [ | ]...
  Qed.

  Next Obligation with discriminate || eauto with *.
    intros d1 d2; split; cbn; unfold Basics.flip.
    all: destruct d1 as [ | ]; destruct d2 as [ | ]...
    all: intros [[ | ] [ | ]]...
  Qed.

  Lemma dir_compare_spec_LT :
    forall lhs : dir_t,
    forall rhs : dir_t, dir_compare lhs rhs = Lt ->
    lhs =< rhs /\ ~ lhs == rhs.
  Proof with discriminate || eauto.
    cbn; intros [ | ] [ | ] H...
    split...
  Qed.

  Lemma dir_compare_spec_EQ :
    forall lhs : dir_t,
    forall rhs : dir_t,
    dir_compare lhs rhs = Eq ->
    lhs == rhs.
  Proof with discriminate || eauto.
    cbn; intros [ | ] [ | ] H...
  Qed.

  Lemma dir_compare_spec_GT :
    forall lhs : dir_t,
    forall rhs : dir_t,
    dir_compare lhs rhs = Gt ->
    rhs =< lhs /\ ~ lhs == rhs.
  Proof with discriminate || eauto.
    cbn; intros [ | ] [ | ] H...
    split...
  Qed.

  Lemma dir_list_compare_Eq :
    forall lhs : list dir_t,
    forall rhs : list dir_t,
    lex_compare dir_compare lhs rhs = Eq <-> lhs = rhs.
  Proof with discriminate || eauto.
    induction lhs as [ | [ | ] lhs IH]; destruct rhs as [ | [ | ] rhs]; simpl; split; intros H_eq...
    - apply eq_congruence, IH...
    - apply IH; congruence.
    - apply eq_congruence, IH...
    - apply IH; congruence.
  Qed.

  Definition index_t : Set :=
    list dir_t
  .

  Definition encoding_index (idx : index_t) : nat :=
    fold_right (dir_t_rec (fun _ => nat -> nat) (fun acc : nat => 2 * acc) (fun acc : nat => 2 * acc + 1)) 1 (rev idx)
  .

  Lemma encoding_index_last (idx : index_t) (d : dir_t) :
    encoding_index (idx ++ [d]) =
    match d with
    | Dir_left => 2 * encoding_index idx
    | Dir_right => 2 * encoding_index idx + 1
    end.
  Proof.
    unfold encoding_index.
    rewrite list_rev_cons.
    destruct d; reflexivity.
  Qed.

  Lemma decoding_index :
    forall code : nat,
    code <> 0 ->
    {idx : index_t | encoding_index idx = code}.
  Proof with lia || eauto.
    strong_rec. intros [ | n']; [contradiction | set (n := S n')].
    destruct n' as [ | n'']; intros acc_hyp H_n_ne_0.
    - exists ([])...
    - assert (claim1 := Nat.div_mod n 2 (S_eq_0_elim 1)).
      destruct (Nat.mod_bound_pos n 2 (le_intro_0_le_n n) (le_S 1 1 (le_n 1))) as [claim2 claim3].
      assert (claim4 : leq (n / 2) n).
      { apply le_implies_leq... }
      assert (claim5 : n / 2 <> n)...
      assert (claim6 : n / 2 <> 0)...
      destruct (acc_hyp (n / 2) claim4 claim5 claim6) as [idx H_idx].
      destruct (n mod 2) as [ | [ | n_mod_2]] eqn: H_obs...
      { exists (idx ++ [Dir_left]); rewrite encoding_index_last... }
      { exists (idx ++ [Dir_right]); rewrite encoding_index_last... }
  Qed.

  Lemma encoding_index_range :
    forall code : nat,
    (exists idx : index_t, encoding_index idx = code) <-> code <> 0.
  Proof with lia || eauto.
    intros n; split.
    - intros [idx H_idx]; subst n; pattern idx; revert idx; apply list_reversed_induction; cbn...
      intros idx d H_ne; rewrite encoding_index_last; destruct d...
    - intros H_n_ne_0. destruct (decoding_index n H_n_ne_0) as [idx H_idx]...
  Qed.

  Lemma encoding_index_injective :
    forall idx1 : index_t,
    forall idx2 : index_t,
    encoding_index idx1 = encoding_index idx2 ->
    idx1 = idx2.
  Proof with lia || eauto.
    assert (claim1 : forall idx : index_t, encoding_index idx > 0).
    { intros idx. enough (to_show : encoding_index idx <> 0)... pose (proj1 (encoding_index_range (encoding_index idx)))... }
    intros idx1; pattern idx1; revert idx1; apply list_reversed_induction; cbn...
    - intros idx2; pattern idx2; revert idx2; apply list_reversed_induction; cbn...
      intros idx2 d2 _. pose (claim1 idx2). rewrite encoding_index_last; destruct d2...
    - intros idx1 d1 IH.
      intros idx2; pattern idx2; revert idx2; apply list_reversed_induction; cbn...
      + pose (claim1 idx1). rewrite encoding_index_last. destruct d1...
      + intros idx2 d2 _.
        do 2 rewrite encoding_index_last; destruct d1; destruct d2...
        { intros H_eq. apply (eq_congruence (fun idx : index_t => idx ++ [Dir_left]) idx1 idx2). apply IH... }
        { intros H_eq. apply (eq_congruence (fun idx : index_t => idx ++ [Dir_right]) idx1 idx2). apply IH... }
  Qed.

  End INDICES_OF_BINARY_TREES.

  Section BINARY_TREES.

  Variable Elem : Set.

  Inductive bintree : Set :=
  | BT_null : bintree
  | BT_node (lchild : bintree) (element : Elem) (rchild : bintree) : bintree
  .

  End BINARY_TREES.

  Global Arguments bintree {Elem}.

End BinTree.
