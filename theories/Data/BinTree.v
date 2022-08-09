Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module BinTree.

  Import ListNotations.

  Inductive bintree (A : Type) : Type :=
  | BTnull : bintree A
  | BTnode (t_l : bintree A) (x : A) (t_r : bintree A) : bintree A
  .

  Global Arguments BTnull {A}.
  Global Arguments BTnode {A} (t_l) (x) (t_r).

  Section ACCESSORIES.

  Context {A : Type}.

  Local Notation bintree := (bintree A).

  Fixpoint getHeight (t : bintree) {struct t} : nat :=
    match t with
    | BTnull => 0
    | BTnode t_l x t_r => 1 + max (getHeight t_l) (getHeight t_r)
    end
  .

  Section BFS.

  Fixpoint rk_bt (t : bintree) {struct t} : nat :=
    match t with
    | BTnull => 1
    | BTnode t_l x t_r => 1 + rk_bt t_l + rk_bt t_r
    end
  .

  Definition rk_queue (ts : list bintree) : nat :=
    list_sum (map rk_bt ts)
  .

  Inductive bfs_spec : list bintree -> list A -> Prop :=
  | bfs_nil
    : bfs_spec [] []
  | bfs_cons_null (ts : list bintree) (xs : list A)
    (IH_SPEC : bfs_spec ts xs)
    : bfs_spec (BTnull :: ts) xs
  | bfs_cons_node (t_l : bintree) (x : A) (t_r : bintree) (ts : list bintree) (xs : list A)
    (IH_SPEC : bfs_spec ([t_l; t_r] ++ ts) xs)
    : bfs_spec (BTnode t_l x t_r :: ts) (x :: xs)
  .

  Definition bfs_withSpec (ts : list bintree)
    : {xs : list A | forall xs' : list A, bfs_spec ts xs' <-> xs = xs'}.
  Proof.
    assert (RECURSOR : forall ts : list bintree, Acc (fun lhs : list bintree => fun rhs : list bintree => rk_queue lhs < rk_queue rhs) ts).
    { exact (well_founded_relation_on_image rk_queue Nat.lt (@lt_strong_ind (@Acc nat lt) (@Acc_intro nat lt))). }
    induction (RECURSOR ts) as [ts H_acc_inv IH]. clear H_acc_inv RECURSOR. destruct ts as [ | [ | t_l x t_r]].
    - exists ([]). intros xs'. split.
      + intros SPEC. inversion SPEC; subst. reflexivity.
      + intros ?; subst xs'. econstructor 1.
    - assert (IH_rk : rk_queue ts < rk_queue (BTnull :: ts)).
      { cbn. eapply le_intro_S_n_le_S_m. reflexivity. }
      pose proof (IH ts IH_rk) as [xs IH_bfs].
      exists (xs). intros xs'. split.
      + intros SPEC. inversion SPEC; subst. eapply IH_bfs. exact (IH_SPEC).
      + intros ?; subst xs'. econstructor 2. eapply IH_bfs. reflexivity.
    - assert (IH_rk : rk_queue ([t_l; t_r] ++ ts) < rk_queue (BTnode t_l x t_r :: ts)).
      { cbn. eapply le_intro_S_n_le_S_m. rewrite Nat.add_assoc. reflexivity. }
      pose proof (IH ([t_l; t_r] ++ ts) IH_rk) as [xs IH_bfs].
      exists (x :: xs). intros xs'. split.
      + intros SPEC. inversion SPEC; subst. eapply eq_congruence. eapply IH_bfs. exact (IH_SPEC).
      + intros ?; subst xs'. econstructor 3. eapply IH_bfs. reflexivity.
  Defined.

  Definition bfs (ts : list bintree) : list A :=
    proj1_sig (bfs_withSpec ts)
  .

  Lemma bfs_spec_iff (ts : list bintree) (xs : list A)
    : bfs_spec ts xs <-> bfs ts = xs.
  Proof. revert xs. exact (proj2_sig (bfs_withSpec ts)). Qed.

  Theorem bfs_unfold (ts : list bintree) :
    bfs ts =
    match ts with
    | [] => []
    | BTnull :: ts' => bfs ts'
    | BTnode t_l x t_r :: ts' => x :: bfs ([t_l; t_r] ++ ts')
    end.
  Proof.
    destruct ts as [ | [ | t_l x t_r] ts']; eapply bfs_spec_iff; econstructor.
    all: eapply bfs_spec_iff; reflexivity.
  Qed.

  End BFS.

  End ACCESSORIES.

End BinTree.
