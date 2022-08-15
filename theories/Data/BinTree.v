Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module BinaryTrees.

  Import ListNotations.

  Inductive direction : Set := LeftDir | RightDir.

  Definition encode (ds : list direction) : nat := fold_left (fun i : nat => direction_rect (fun _ : direction => nat) (2 * i + 1) (2 * i + 2)) ds 0.

  Lemma encode_inj (ds1 : list direction) (ds2 : list direction)
    (ENCODE_EQ : encode ds1 = encode ds2)
    : ds1 = ds2.
  Proof with lia || eauto.
    revert ENCODE_EQ. unfold encode; do 2 rewrite <- fold_left_rev_right.
    intros ENCODE_EQ; eapply rev_inj; revert ENCODE_EQ.
    generalize (rev ds2) as xs2. generalize (rev ds1) as xs1. clear ds1 ds2.
    set (myF := fold_right (fun d : direction => fun i : nat => direction_rect (fun _ : direction => nat) (2 * i + 1) (2 * i + 2) d) 0).
    induction xs1 as [ | x1 xs1 IH], xs2 as [ | x2 xs2]; simpl...
    - destruct x2; simpl direction_rect...
    - destruct x1; simpl direction_rect...
    - destruct x1; destruct x2; simpl direction_rect...
      all: intros ?; assert (claim1 : myF xs1 = myF xs2)...
      all: eapply eq_congruence...
  Qed.

  Lemma encode_last (ds : list direction) (d : direction) :
    encode (ds ++ [d]) =
    match d with
    | LeftDir => 2 * encode ds + 1
    | RightDir => 2 * encode ds + 2
    end.
  Proof.
    unfold encode at 1. rewrite <- fold_left_rev_right, rev_unit.
    unfold fold_right, encode. rewrite <- fold_left_rev_right.
    now destruct d as [ | ].
  Qed.

  Lemma decodable (idx : nat)
    : {ds : list direction | encode ds = idx}.
  Proof with lia || eauto.
    induction idx as [[ | i'] IH] using NotherianRecursion.
    - exists ([])...
    - set (i := S i'). destruct (i mod 2) as [ | [ | i_mod_2]] eqn: H_obs.
      + assert (claim1 : i = 2 * ((i - 2) / 2) + 2).
        { eapply positive_even with (n := (i - 2) / 2)... }
        assert (claim2 : (i - 2) / 2 < i)...
        pose proof (IH ((i - 2) / 2) claim2) as [ds H_ds].
        exists (ds ++ [RightDir]).
        unfold encode. rewrite fold_left_last. unfold direction_rect at 1.
        unfold encode in H_ds. rewrite H_ds...
      + assert (claim1 : i = 2 * ((i - 1) / 2) + 1).
        { eapply positive_odd with (n := (i - 1) / 2)... }
        assert (claim2 : (i - 1) / 2 < i)...
        pose proof (IH ((i - 1) / 2) claim2) as [ds H_ds].
        exists (ds ++ [LeftDir]).
        unfold encode. rewrite fold_left_last. unfold direction_rect at 1.
        unfold encode in H_ds. rewrite H_ds...
      + pose proof (Nat.mod_bound_pos i 2)...
  Defined.

  Definition decode (idx : nat) : list direction := proj1_sig (decodable idx).

  Section BINARY_TREE.

  Context {A : Type}.

  Inductive bintree : Type := BTnull | BTnode (t_l : bintree) (x : A) (t_r : bintree).

  Fixpoint getHeight (t : bintree) {struct t} : nat :=
    match t with
    | BTnull => 0
    | BTnode t_l x t_r => 1 + max (getHeight t_l) (getHeight t_r)
    end
  .

  Fixpoint getSize (t : bintree) {struct t} : nat :=
    match t with
    | BTnull => 0
    | BTnode t_l x t_r => 1 + (getSize t_l + getSize t_r)
    end
  .

  Definition getLeftChild (t : bintree) : option bintree :=
    match t with
    | BTnull => None
    | BTnode t_l x t_r => Some t_l
    end
  .

  Definition getRightChild (t : bintree) : option bintree :=
    match t with
    | BTnull => None
    | BTnode t_l x t_r => Some t_r
    end
  .

  Definition getKey (t : bintree) : option A :=
    match t with
    | BTnull => None
    | BTnode t_l x t_r => Some x
    end
  .

  Definition goto : list direction -> bintree -> option bintree :=
    let k_step := @direction_rect _ (fun k : bintree -> option bintree => k <=< getLeftChild) (fun k : bintree -> option bintree => k <=< getRightChild) in
    let k_base := @Some _ in
    fold_right (A := bintree -> option bintree) (B := direction) k_step k_base
  .

  Lemma goto_unfold (ds : list direction) (t : bintree) :
    goto ds t =
    match ds with
    | [] => Some t
    | LeftDir :: ds' =>
      match t with
      | BTnull => None
      | BTnode t_l x t_r => goto ds' t_l
      end
    | RightDir :: ds' =>
      match t with
      | BTnull => None
      | BTnode t_l x t_r => goto ds' t_r
      end
    end.
  Proof with try reflexivity.
    destruct ds as [ | [ | ] ds']...
    all: destruct t as [ | t_l x t_r]...
  Qed.

  Definition lookup (t : bintree) (ds : list direction) : option A :=
    (getKey <=< goto ds) t
  .

  Definition toList (t : bintree) : list A :=
    map (lookup t ∘ decode) (seq 0 (2 ^ getHeight t)) >>= maybe [] pure
  .

  Section COMPLETE_TREE.

  Definition isComplete (t : bintree) : Prop :=
    forall idx : nat, idx < getSize t -> lookup t (decode idx) <> None
  .

  End COMPLETE_TREE.

  Section BREADTH_FIRST_SEARCH.

  Fixpoint rk_bt (t : bintree) {struct t} : nat :=
    match t with
    | BTnull => 1
    | BTnode t_l x t_r => 1 + rk_bt t_l + rk_bt t_r
    end
  .

  Definition rk_queue (ts : list bintree) : nat := list_sum (map rk_bt ts).

  Inductive bfsAux_spec : list bintree -> list A -> Prop :=
  | bfsAux_nil
    : bfsAux_spec [] []
  | bfsAux_cons_null (ts : list bintree) (xs : list A)
    (IH_SPEC : bfsAux_spec ts xs)
    : bfsAux_spec (BTnull :: ts) xs
  | bfsAux_cons_node (t_l : bintree) (x : A) (t_r : bintree) (ts : list bintree) (xs : list A)
    (IH_SPEC : bfsAux_spec ([t_l; t_r] ++ ts) xs)
    : bfsAux_spec (BTnode t_l x t_r :: ts) (x :: xs)
  .

  Definition bfsAux_withSpec (ts : list bintree)
    : {xs : list A | forall xs' : list A, bfsAux_spec ts xs' <-> xs = xs'}.
  Proof.
    assert (WF_REC : forall ts : list bintree, Acc (fun lhs : list bintree => fun rhs : list bintree => rk_queue lhs < rk_queue rhs) ts).
    { exact (well_founded_relation_on_image rk_queue Nat.lt (@lt_strong_ind (@Acc nat Nat.lt) (@Acc_intro nat Nat.lt))). }
    induction (WF_REC ts) as [ts H_acc_inv IH]. clear H_acc_inv WF_REC. destruct ts as [ | [ | t_l x t_r] ts].
    - exists ([]). intros xs'. split.
      + intros SPEC. inversion SPEC; subst. reflexivity.
      + intros ?; subst xs'. econstructor 1.
    - assert (IH_rk : rk_queue ts < rk_queue (BTnull :: ts)).
      { cbn. eapply le_intro_S_n_le_S_m. reflexivity. }
      pose proof (IH ts IH_rk) as [xs IH_xs].
      exists (xs). intros xs'. split.
      + intros SPEC. inversion SPEC; subst. eapply IH_xs. exact (IH_SPEC).
      + intros ?; subst xs'. econstructor 2. eapply IH_xs. reflexivity.
    - assert (IH_rk : rk_queue ([t_l; t_r] ++ ts) < rk_queue (BTnode t_l x t_r :: ts)).
      { cbn. eapply le_intro_S_n_le_S_m. rewrite Nat.add_assoc. reflexivity. }
      pose proof (IH ([t_l; t_r] ++ ts) IH_rk) as [xs IH_xs].
      exists (x :: xs). intros xs'. split.
      + intros SPEC. inversion SPEC; subst. eapply eq_congruence. eapply IH_xs. exact (IH_SPEC).
      + intros ?; subst xs'. econstructor 3. eapply IH_xs. reflexivity.
  Defined.

  Definition bfsAux (ts : list bintree) : list A := proj1_sig (bfsAux_withSpec ts).

  Lemma bfsAux_spec_iff (ts : list bintree) (xs : list A)
    : bfsAux_spec ts xs <-> bfsAux ts = xs.
  Proof. revert xs. exact (proj2_sig (bfsAux_withSpec ts)). Qed.

  Theorem bfsAux_unfold (ts : list bintree) :
    bfsAux ts =
    match ts with
    | [] => []
    | BTnull :: ts' => bfsAux ts'
    | BTnode t_l x t_r :: ts' => x :: bfsAux ([t_l; t_r] ++ ts')
    end.
  Proof.
    destruct ts as [ | [ | t_l x t_r] ts']; eapply bfsAux_spec_iff; econstructor.
    all: eapply bfsAux_spec_iff; reflexivity.
  Qed.

  Definition bfs (t : bintree) : list A := bfsAux [t].

  End BREADTH_FIRST_SEARCH.

  End BINARY_TREE.

  Global Arguments bintree : clear implicits.

End BinaryTrees.
