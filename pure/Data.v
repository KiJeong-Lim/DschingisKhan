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

  Definition addIndices_aux {A : Type} : list A -> nat -> list (A * nat) :=
    fold_right (fun x acc n => (x, n) :: acc (1 + n)) (fun n => [])
  .

  Definition addIndices {A : Type} (xs : list A) : list (A * nat) :=
    addIndices_aux xs 0
  .

  Definition update {A : Type} (xs : list A) (i0 : nat) (x0 : A) : list A :=
    map (fun it => if Nat.eq_dec (snd it) i0 then x0 else fst it) (addIndices xs)
  .

  Definition swap_aux {A : Type} (xs : list A) (i1 : nat) (i2 : nat) (x : A) (i : nat) : A :=
    (if Nat.eq_dec i i1 then nth i2 xs x else (if Nat.eq_dec i i2 then nth i1 xs x else (x)))
  .

  Definition swap {A : Type} (xs : list A) (i1 : nat) (i2 : nat) : list A :=
    map (uncurry (swap_aux xs i1 i2)) (addIndices xs)
  .

  End ListAccessories.

  Section ListTheory.

  Theorem list_extensionality {A : Type} (xs1 : list A) (xs2 : list A)
    : xs1 = xs2 <-> (forall i x, nth_error xs1 i = Some x <-> nth_error xs2 i = Some x).
  Proof with discriminate || eauto.
    split.
    - intros ?; subst xs2. reflexivity.
    - revert xs2; induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; intros H_ext_eq...
      + pose proof (proj2 (H_ext_eq 0 x2) (eq_reflexivity (Some x2)))...
      + pose proof (proj1 (H_ext_eq 0 x1) (eq_reflexivity (Some x1)))...
      + apply eq_congruence2.
        { pose proof (proj2 (H_ext_eq 0 x2) (eq_reflexivity (Some x2))); apply Some_inj... }
        { apply IH. intros i x; exact (H_ext_eq (S i) x). }
  Qed.

  Lemma addIndices_aux_unfold {A : Type} (xs : list A) (n : nat) :
    addIndices_aux xs n =
    match xs with
    | [] => []
    | hd_xs :: tl_xs => (hd_xs, n) :: addIndices_aux tl_xs (S n)
    end.
  Proof. induction xs as [ | x xs IH]; simpl; eauto. Qed.

  Lemma addIndices_unfold {A : Type} (xs : list A) :
    addIndices xs =
    match xs with
    | [] => []
    | hd_xs :: tl_xs => (hd_xs, 0) :: map (fun it => (fst it, 1 + snd it)) (addIndices tl_xs)
    end.
  Proof with eauto.
    unfold addIndices; cbn. rename xs into xs1. generalize 0 as n; intros n.
    rewrite addIndices_aux_unfold at 1. destruct xs1 as [ | x1 xs1]...
    apply eq_congruence. clear x1; revert n; induction xs1 as [ | x1 xs1 IH]; simpl...
    intros n; apply eq_congruence; exact (IH (S n)).
  Qed.

  Lemma map_listExt {A : Type} {B : Type} (xs : list A) (f : A -> B)
    : forall i y, nth_error (map f xs) i = Some y <-> (exists x, nth_error xs i = Some x /\ y = f x).
  Proof with lia || eauto.
    intros i y. split; [intros y_is | intros [x [x_is y_eq_f_x]]].
    - assert (x_exists : exists x : A, nth_error xs i = Some x).
      { apply isSome_intro, nth_error_Some in y_is; rewrite map_length in y_is.
        destruct (nth_error xs i) as [x | ] eqn: H_obs; [exists (x) | apply nth_error_None in H_obs]...
      }
      destruct x_exists as [x x_is]. exists x; split...
      rewrite map_nth_error with (d := x) in y_is... apply Some_inj in y_is...
    - rewrite map_nth_error with (d := x)... apply eq_congruence...
  Qed.

  Lemma addIndices_listExt {A : Type} (xs : list A)
    : forall i x n, nth_error (addIndices xs) i = Some (x, n) <-> (nth_error xs i = Some x /\ i = n).
  Proof with eauto.
    induction xs as [ | x1 xs1 IH]; rewrite addIndices_unfold; simpl.
    - intros [ | i'] x n; now split.
    - intros [ | i'] x n; split; simpl.
      + intros H_eq. now split; congruence.
      + intros [x_is n_is]; congruence.
      + intros H_obs. apply map_listExt in H_obs. destruct H_obs as [[_x _n] [H_obs _obs_is]].
        pose proof (eq_congruence fst _ _ _obs_is) as _x_is.
        pose proof (eq_congruence snd _ _ _obs_is) as _n_is.
        simpl in *; subst x n. destruct (proj1 (IH i' _x _n) H_obs) as [H_fst H_snd]...
      + intros [H_fst H_snd]. apply map_listExt. exists (x, i'); split... apply IH...
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
