Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module LinkedLists.

  Import ListNotations EqFacts MyUtilities BasicSetoidTheory BasicPosetTheory.

  Section ListAccessories.

  Definition add_indices {A : Type} (xs : list A) : list (A * nat) :=
    (combine xs (seq 0 (length xs)))
  .

  Definition upd {A : Type} (xs : list A) (i0 : nat) (x0 : A) : list A :=
    map (fun it => if Nat.eq_dec (snd it) i0 then x0 else fst it) (add_indices xs)
  .

  Definition swap_aux {A : Type} (xs : list A) (i1 : nat) (i2 : nat) (x : A) (i : nat) : A :=
    if Nat.eq_dec i i1 then nth i2 xs x else
    if Nat.eq_dec i i2 then nth i1 xs x else
    x
  .

  Definition swap {A : Type} (xs : list A) (i1 : nat) (i2 : nat) : list A :=
    map (uncurry (swap_aux xs i1 i2)) (add_indices xs)
  .

  End ListAccessories.

  Section ListTheory.

  Theorem list_extensionality {A : Type} (xs1 : list A) (xs2 : list A) :
    xs1 = xs2 <-> (forall i, nth_error xs1 i = nth_error xs2 i).
  Proof with discriminate || eauto.
    revert xs1 xs2; cbn.
    induction xs1 as [ | x1 xs1 IH]; intros [ | x2 xs2]; simpl in *; split; intros H_eq...
    - pose proof (H_eq 0)...
    - pose proof (H_eq 0)...
    - rewrite H_eq...
    - apply eq_congruence2.
      + exact (Some_inj x1 x2 (H_eq 0)).
      + exact (proj2 (IH xs2) (fun i => H_eq (S i))).
  Qed.

  End ListTheory.

End LinkedLists.

Module BinaryTrees.

  Import ListNotations EqFacts MyUtilities BasicSetoidTheory BasicPosetTheory LinkedLists.

  Inductive bintree (Elem : Type) : Type :=
  | BT_null : bintree Elem
  | BT_node (lchild : bintree Elem) (elements : Elem) (rchild : bintree Elem) : bintree Elem
  .

  Global Arguments BT_null {Elem}.
  Global Arguments BT_node {Elem}.

  Section BinaryTreeAccessories.

  Definition option2list {A : Type} : option A -> list A :=
    maybe [] (fun x => [x])
  .

  Definition pair2list {A : Type} : A * A -> list A :=
    uncurry (fun x1 x2 => [x1; x2])
  .

  End BinaryTreeAccessories.

End BinaryTrees.
