Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module MyFin.

  Definition evalFin {n : nat} (i : Fin n) : nat := proj1_sig (runFin i).

  Lemma evalFin_unfold {n : nat} (i : Fin n) :
    evalFin i =
    match i with
    | FZ => O
    | FS i' => S (evalFin i')
    end.
  Proof. destruct i; reflexivity. Qed.

  Lemma evalFin_inj {n : nat} (i1 : Fin n) (i2 : Fin n)
    (hyp_eq : evalFin i1 = evalFin i2)
    : i1 = i2.
  Proof.
    unfold evalFin in hyp_eq.
    rewrite <- getFin_runFin_id with (i := i1).
    rewrite <- getFin_runFin_id with (i := i2).
    destruct (runFin i1) as [m1 hyp_lt1].
    destruct (runFin i2) as [m2 hyp_lt2].
    cbn in *. subst m1. eapply eq_congruence, le_pirrel.
  Qed.

  Definition incrFin {m : nat} : forall n : nat, Fin m -> Fin (n + m) :=
    fix incrFin_fix (n : nat) (i : Fin m) {struct n} : Fin (n + m) :=
    match n as x return Fin (x + m) with
    | O => i
    | S n' => FS (incrFin_fix n' i)
    end
  .

  Lemma incrFin_spec {m : nat} (n : nat) (i : Fin m)
    : evalFin (incrFin n i) = n + evalFin i.
  Proof with eauto.
    induction n as [ | n IH]; simpl...
    rewrite evalFin_unfold. eapply eq_congruence...
  Qed.

End MyFin.

Module MyVec.

  Global Open Scope vector_scope.

End MyVec.
