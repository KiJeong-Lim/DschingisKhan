Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module BinaryTrees.

  Import ListNotations EqFacts MyUtilities BasicSetoidTheory BasicPosetTheory.

  Inductive bintree (Elem : Type) : Type :=
  | BT_null : bintree Elem
  | BT_node (lchild : bintree Elem) (element : Elem) (rchild : bintree Elem) : bintree Elem
  .

  Global Arguments BT_null {Elem}.
  Global Arguments BT_node {Elem}.

  Section INDICES_OF_BINARY_TREES.

  Inductive dir_t : Set :=
  | Dir_left : dir_t
  | Dir_right : dir_t
  .

  Definition encode (ds : list dir_t) : nat :=
    fold_left (fun code : nat => dir_t_rect (fun _ => nat) (2 * code + 1) (2 * code + 2)) ds 0
  .

  Lemma decode (code : nat) :
    {ds : list dir_t | encode ds = code}.
  Proof with lia || eauto.
    induction code as [[ | n'] IH] using Wf_nat.lt_wf_rect1.
    - exists ([])...
    - set (code := S n').
      destruct (code mod 2) as [ | [ | code_mod_2]] eqn: H_obs.
      + assert (claim1 : code = 2 * ((code - 2) / 2) + 2).
        { apply (positive_even code ((code - 2) / 2))... }
        assert (claim2 : (code - 2) / 2 < code)...
        destruct (IH ((code - 2) / 2) claim2) as [ds H_ds].
        exists (ds ++ [Dir_right]).
        unfold encode. rewrite fold_left_last. unfold dir_t_rect at 1.
        unfold encode in H_ds. rewrite H_ds...
      + assert (claim1 : code = 2 * ((code - 1) / 2) + 1).
        { apply (positive_odd code ((code - 1) / 2))... }
        assert (claim2 : (code - 1) / 2 < code)...
        destruct (IH ((code - 1) / 2) claim2) as [ds H_ds].
        exists (ds ++ [Dir_left]).
        unfold encode. rewrite fold_left_last. unfold dir_t_rect at 1.
        unfold encode in H_ds. rewrite H_ds...
      + pose (Nat.mod_bound_pos code 2)...
  Defined.

(*
  Compute (proj1_sig (decode 14)).
  (* = [Dir_right; Dir_right; Dir_right] *)
  Compute (proj1_sig (decode 15)).
  (* = [Dir_left; Dir_left; Dir_left; Dir_left] *)
  Compute (proj1_sig (decode 16)).
  (* = [Dir_left; Dir_left; Dir_left; Dir_right] *)
*)

  Lemma encode_inj :
    forall ds1 : list dir_t,
    forall ds2 : list dir_t,
    encode ds1 = encode ds2 ->
    ds1 = ds2.
  Proof with lia || eauto.
    unfold encode; intros ds1 ds2. do 2 rewrite <- fold_left_rev_right.
    intros H_eq; apply list_rev_inj; revert H_eq.
    generalize (rev ds2) as xs2. generalize (rev ds1) as xs1. clear ds1 ds2.
    set (myF := fold_right (fun y : dir_t => fun x : nat => dir_t_rect (fun _ : dir_t => nat) (2 * x + 1) (2 * x + 2) y) 0).
    induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
    - destruct x2; simpl dir_t_rect...
    - destruct x1; simpl dir_t_rect...
    - destruct x1; destruct x2; simpl dir_t_rect...
      all: intros H_eq; assert (claim1 : myF xs1 = myF xs2)...
      all: apply f_equal...
  Qed.

  End INDICES_OF_BINARY_TREES.

  Fixpoint option_subtree {A : Type} (ds : list dir_t) (t : bintree A) {struct ds} : option (bintree A) :=
    match ds with
    | [] => Some t
    | d :: ds' =>
      match t with
      | BT_null => None
      | BT_node l e r => option_subtree ds' (dir_t_rect (fun _ => bintree A) l r d)
      end
    end
  .

End BinaryTrees.
