Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module BNat.

  Inductive bnat : Set :=
  | b0            : bnat (* = 0 *)
  | bO (b : bnat) : bnat (* = b * 2 *)
  | bI (b : bnat) : bnat (* = b * 2 + 1 *)
  .

  Fixpoint to_nat (b : bnat) {struct b} : nat :=
    match b with
    | b0 => 0
    | bO b' => to_nat b' * 2
    | bI b' => to_nat b' * 2 + 1
    end
  .

  Global Instance bnat_isSetoid : isSetoid bnat :=
    { eqProp (lhs : bnat) (rhs : bnat) := to_nat lhs = to_nat rhs
    ; eqProp_Equivalence := relation_on_image_liftsEquivalence to_nat eq_equivalence
    }
  .

  Global Instance bnatEqDec
    : EqDec bnat.
  Proof with try ((left; congruence) || (right; congruence)).
    change (forall lhs : bnat, forall rhs : bnat, {lhs = rhs} + {lhs <> rhs}).
    induction lhs as [ | b IH | b IH], rhs as [ | b' | b']...
    - pose proof (IH b') as [H_EQ | H_NE]...
    - pose proof (IH b') as [H_EQ | H_NE]...
  Defined.

  Fixpoint incr_bnat (b : bnat) {struct b} : bnat :=
    match b with
    | b0 => bI b0
    | bO b' => bI b'
    | bI b' => bO (incr_bnat b')
    end
  .

  Lemma to_nat_incr_comm (b : bnat)
    : to_nat (incr_bnat b) = to_nat b + 1.
  Proof.
    induction b as [ | b IH | b IH].
    - reflexivity.
    - reflexivity.
    - simpl. rewrite IH. lia.
  Qed.

  Fixpoint of_nat (n : nat) {struct n} : bnat :=
    match n with
    | O => b0
    | S n' => incr_bnat (of_nat n')
    end
  .

  Lemma to_nat_of_nat_id (n : nat)
    : to_nat (of_nat n) = n.
  Proof.
    induction n as [ | n IH].
    - reflexivity.
    - simpl. rewrite to_nat_incr_comm. rewrite IH. lia.
  Qed.

  Lemma of_nat_twice (n : nat)
    (n_ne_0 : n <> 0)
    : of_nat (n * 2) = bO (of_nat n).
  Proof.
    - induction n as [ | n IH].
      + contradiction.
      + destruct n as [ | n'].
        * reflexivity.
        * simpl. simpl in IH. rewrite IH.
          { reflexivity. }
          { discriminate. }
  Qed.

  Fixpoint norm_bnat (b : bnat) {struct b} : bnat :=
    match b with
    | b0 => b0
    | bO b' =>
      match norm_bnat b' with
      | b0 => b0
      | nb' => bO nb'
      end
    | bI b' => bI (norm_bnat b')
    end
  .

  Example norm_bnat_example1
    : norm_bnat (bO (bO (bO (b0))))
    = (b0).
  Proof. reflexivity. Qed.

  Example norm_bnat_example2
    : norm_bnat (bO (bO (bI (b0))))
    = (bO (bO (bI (b0)))).
  Proof. reflexivity. Qed.

  Example norm_bnat_example3
    : norm_bnat (bO (bI (bO (b0))))
    = (bO (bI (b0))).
  Proof. reflexivity. Qed.

  Lemma to_nat_eq_0_implies_norm_eq_0 (b : bnat)
    (to_nat_returns_0 : to_nat b = 0)
    : norm_bnat b = b0.
  Proof.
    induction b as [ | b IH | b IH].
    - reflexivity.
    - simpl. rewrite IH.
      + reflexivity.
      + simpl in to_nat_returns_0. lia.
    - simpl. simpl in to_nat_returns_0. lia.
  Qed.

  Lemma of_nat_returns_0_iff (n : nat)
    : of_nat n = b0 <-> 0 = n.
  Proof.
    split.
    - induction n as [ | n IH]; intros of_nat_returns_0.
      + reflexivity.
      + simpl in of_nat_returns_0. now destruct (of_nat n).
    - intros H_EQ; subst n. reflexivity.
  Qed.

  Lemma of_nat_to_nat_twice (b : bnat)
    (b_ne_0 : norm_bnat b <> b0)
    : of_nat (to_nat b * 2) = bO (of_nat (to_nat b)).
  Proof.
    induction b as [ | b IH | b IH].
    - contradiction.
    - enough (H_NE : to_nat (bO b) <> 0) by now rewrite of_nat_twice.
      destruct b as [ | b' | b'].
      + contradiction.
      + intros H_false. contradiction b_ne_0. eapply to_nat_eq_0_implies_norm_eq_0. eassumption.
      + intros H_false. contradiction b_ne_0. eapply to_nat_eq_0_implies_norm_eq_0. eassumption.
    - enough (H_NE : to_nat (bI b) <> 0) by now rewrite of_nat_twice.
      simpl. lia.
  Qed.

  Theorem of_nat_to_nat_norm (b : bnat)
    : of_nat (to_nat b) = norm_bnat b.
  Proof with reflexivity || discriminate || trivial.
    induction b as [ | b IH | b IH]...
    - simpl.
      pose proof (claim := of_nat_to_nat_twice b).
      destruct (norm_bnat b) as [ | nb' | nb'] eqn: H_obs.
      + destruct b as [ | b' | b']...
        now replace (to_nat (bO b')) with (0) by now eapply of_nat_returns_0_iff.
      + rewrite claim...
        now rewrite IH.
      + rewrite claim...
        now rewrite IH.
    - simpl. replace (to_nat b * 2 + 1) with (S (to_nat b * 2)) by lia.
      simpl.
      pose proof (claim := of_nat_to_nat_twice b).
      destruct (norm_bnat b) as [ | nb' | nb'] eqn: H_obs.
      + destruct b as [ | b' | b']...
        now replace (to_nat (bO b')) with (0) by now eapply of_nat_returns_0_iff.
      + rewrite claim...
        now rewrite IH.
      + rewrite claim...
        now rewrite IH.
  Qed.

  Corollary bnat_eq_thm (lhs : bnat) (rhs : bnat)
    : lhs == rhs <-> norm_bnat lhs = norm_bnat rhs.
  Proof.
    split; intros H_EQ.
    - rewrite <- of_nat_to_nat_norm with (b := lhs).
      rewrite <- of_nat_to_nat_norm with (b := rhs).
      eapply eq_congruence with (f := of_nat). exact (H_EQ).
    - rewrite <- of_nat_to_nat_norm with (b := lhs) in H_EQ.
      rewrite <- of_nat_to_nat_norm with (b := rhs) in H_EQ.
      apply eq_congruence with (f := to_nat) in H_EQ.
      do 2 rewrite to_nat_of_nat_id in H_EQ. exact (H_EQ).
  Qed.

End BNat.
