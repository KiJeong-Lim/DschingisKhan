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

  Definition index_t : Set :=
    list dir_t
  .

  Definition encoding_index (idx : index_t) : nat :=
    fold_right (dir_t_rect (fun _ => nat -> nat) (fun acc : nat => 2 * acc) (fun acc : nat => 2 * acc + 1)) 1 idx
  .

  Lemma encoding_index_unfold (idx : index_t) :
    encoding_index idx =
    match idx with
    | [] => 1
    | Dir_left :: idx' => 2 * encoding_index idx'
    | Dir_right :: idx' => 2 * encoding_index idx' + 1
    end.
  Proof with eauto.
    induction idx as [ | [ | ] idx IH]; simpl...
  Qed.

  Lemma decoding_index :
    forall code : nat,
    {idx : index_t | code <> 0 -> encoding_index idx = code}.
  Proof with lia || eauto.
    strong_rec. intros [ | n']; [exists ([]); contradiction | set (n := S n')].
    destruct n' as [ | n'']; intros acc_hyp.
    - exists ([])...
    - assert (claim1 := Nat.div_mod n 2 (S_eq_0_elim 1)).
      destruct (Nat.mod_bound_pos n 2 (le_intro_0_le_n n) (le_S 1 1 (le_n 1))) as [claim2 claim3].
      assert (claim4 : leq (n / 2) n).
      { apply le_implies_leq... }
      assert (claim5 : n / 2 <> n)...
      assert (claim6 : n / 2 <> 0)...
      destruct (acc_hyp (n / 2) claim4 claim5) as [idx H_idx].
      destruct (n mod 2) as [ | [ | n_mod_2]] eqn: H_obs...
      { exists (Dir_left :: idx); rewrite encoding_index_unfold... }
      { exists (Dir_right :: idx); rewrite encoding_index_unfold... }
  Qed.

  Lemma encoding_index_range :
    forall code : nat,
    (exists idx : index_t, encoding_index idx = code) <-> code <> 0.
  Proof with lia || eauto.
    intros n; split.
    - intros [idx H_idx]; subst n; induction idx as [ | [ | ] idx IH]; simpl...
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
    induction idx1 as [ | d1 idx1 IH]; destruct idx2 as [ | d2 idx2]...
    - pose (claim1 idx2); rewrite encoding_index_unfold; destruct d2; simpl...
    - pose (claim1 idx1); rewrite encoding_index_unfold; destruct d1; simpl...
    - rewrite encoding_index_unfold with (idx := d1 :: idx1).
      rewrite encoding_index_unfold with (idx := d2 :: idx2).
      destruct d1; destruct d2...
      all: intros H_eq; apply eq_congruence, IH...
  Qed.

  End INDICES_OF_BINARY_TREES.

  Inductive bintree (Elem : Type) : Type :=
  | BT_null : bintree Elem
  | BT_node (lchild : bintree Elem) (element : Elem) (rchild : bintree Elem) : bintree Elem
  .

  Global Arguments BT_null {Elem}.
  Global Arguments BT_node {Elem}.

  Definition btctx (Elem : Type) : Type :=
    list (dir_t * (Elem * bintree Elem))
  .

  Inductive btctx_spec {Elem : Type} (sub_t : bintree Elem) : btctx Elem -> bintree Elem -> Prop :=
  | CtxSpec_top
    : btctx_spec sub_t [] sub_t
  | CtxSpec_left c_l t_l e t_r
    (H_l : btctx_spec sub_t c_l t_l)
    : btctx_spec sub_t (c_l ++ [(Dir_left, (e, t_r))]) (BT_node t_l e t_r)
  | CtxSpec_right c_r t_l e t_r
    (H_r : btctx_spec sub_t c_r t_r)
    : btctx_spec sub_t (c_r ++ [(Dir_right, (e, t_l))]) (BT_node t_l e t_r)
  .

  Local Hint Constructors btctx_spec : core.

  Lemma btctx_spec_refl {Elem : Type} (root : bintree Elem) :
    btctx_spec root [] root.
  Proof.
    constructor 1.
  Qed.

  Lemma btctx_spec_trans {Elem : Type} (root : bintree Elem) :
    forall t1 : bintree Elem,
    forall c1 : btctx Elem,
    btctx_spec t1 c1 root ->
    forall t2 : bintree Elem,
    forall c2 : btctx Elem,
    btctx_spec t2 c2 t1 ->
    btctx_spec t2 (c2 ++ c1) root.
  Proof.
    intros t1 c1 X1; induction X1; intros t2 c2 X2; simpl.
    - rewrite app_nil_r; exact X2.
    - rewrite app_assoc; constructor 2; apply IHX1; exact X2.
    - rewrite app_assoc; constructor 3; apply IHX1; exact X2.
  Qed.

  Definition recover_step_aux {Elem : Type} (d : dir_t) (e : Elem) (t : bintree Elem) : bintree Elem -> bintree Elem :=
    match d with
    | Dir_left => fun t_l : bintree Elem => BT_node t_l e t 
    | Dir_right => fun t_r : bintree Elem => BT_node t e t_r
    end
  .

  Definition recover_step {Elem : Type} : (dir_t * (Elem * bintree Elem)) -> bintree Elem -> bintree Elem :=
    fun it : dir_t * (Elem * bintree Elem) =>
    uncurry (recover_step_aux (fst it)) (snd it)
  .

  Definition recover {Elem : Type} (sub_t : bintree Elem) (c : btctx Elem) : bintree Elem :=
    fold_right recover_step sub_t (rev c)
  .

  Lemma recover_unfold {Elem : Type} (sub_t : bintree Elem) c :
    recover sub_t c =
    match c with
    | [] => sub_t
    | (Dir_left, (e, t_r)) :: c_l => recover (BT_node sub_t e t_r) c_l
    | (Dir_right, (e, t_l)) :: c_r => recover (BT_node t_l e sub_t) c_r
    end.
  Proof with eauto.
    unfold recover at 1; rewrite fold_left_rev_right with (f := recover_step).
    destruct c as [ | [[ | ] [e t]] c]; simpl...
    all: unfold recover at 1; rewrite fold_left_rev_right with (f := recover_step)...
  Qed.

  Lemma recover_last {Elem : Type} (sub_t : bintree Elem) c d e t :
    recover sub_t (c ++ [(d, (e, t))]) =
    match d with
    | Dir_left => BT_node (recover sub_t c) e t 
    | Dir_right => BT_node t e (recover sub_t c)
    end.
  Proof.
    unfold recover at 1; rewrite list_rev_cons, fold_right_unfold; now destruct d.
  Qed.

  Theorem btctx_spec_recover {Elem : Type} sub_t c (root : bintree Elem) :
    btctx_spec sub_t c root <-> recover sub_t c = root.
  Proof with eauto.
    split.
    - intros X; induction X; simpl...
      all: rewrite recover_last, IHX...
    - intros H_eq; subst root; revert sub_t.
      pattern c; revert c; apply list_reversed_induction...
      intros idx [[ | ] [e t]] IH sub_t; rewrite recover_last...
  Qed.

  Lemma btctx_spec_left {Elem : Type} c t_l e t_r (root : bintree Elem) :
    btctx_spec (BT_node t_l e t_r) c root <-> btctx_spec t_l ((Dir_left, (e, t_r)) :: c) root.
  Proof.
    do 2 rewrite btctx_spec_recover.
    now rewrite recover_unfold with (c := (Dir_left, (e, t_r)) :: c).
  Qed.

  Lemma btctx_spec_right {Elem : Type} c t_l e t_r (root : bintree Elem) :
    btctx_spec (BT_node t_l e t_r) c root <-> btctx_spec t_r ((Dir_right, (e, t_l)) :: c) root.
  Proof.
    do 2 rewrite btctx_spec_recover.
    now rewrite recover_unfold with (c := (Dir_right, (e, t_l)) :: c).
  Qed.

End BinTree.
