Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Wf.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module BinaryTrees.

  Import ListNotations EqFacts MyUtilities BasicSetoidTheory BasicPosetTheory.

  Section INDICES_OF_BINARY_TREES.

  Inductive dir_t : Set :=
  | Dir_left : dir_t
  | Dir_right : dir_t
  .

  Definition encode : list dir_t -> nat :=
    fun ds : list dir_t =>
    fold_left (fun code : nat => @dir_t_rect (fun _ : dir_t => nat) (2 * code + 1) (2 * code + 2)) ds 0
  .

  Lemma encode_inj :
    forall ds1 : list dir_t,
    forall ds2 : list dir_t,
    encode ds1 = encode ds2 ->
    ds1 = ds2.
  Proof with lia || eauto.
    unfold encode. intros ds1 ds2. do 2 rewrite <- fold_left_rev_right.
    intros H_eq. apply list_rev_inj. revert H_eq.
    generalize (rev ds2) as xs2. generalize (rev ds1) as xs1. clear ds1 ds2.
    set (myF := fold_right (fun d : dir_t => fun i : nat => @dir_t_rect (fun _ : dir_t => nat) (2 * i + 1) (2 * i + 2) d) 0).
    induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
    - destruct x2; simpl dir_t_rect...
    - destruct x1; simpl dir_t_rect...
    - destruct x1; destruct x2; simpl dir_t_rect...
      all: intros H_eq; assert (claim1 : myF xs1 = myF xs2)...
      all: apply eq_congruence...
  Qed.

  Lemma decodable :
    forall code : nat,
    {ds : list dir_t | encode ds = code}.
  Proof with lia || eauto.
    induction code as [[ | code'] IH] using Wf_nat.lt_wf_rect1.
    - exists ([])...
    - set (code := S code').
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

  Definition decode : nat -> list dir_t :=
    fun code : nat =>
    proj1_sig (decodable code)
  .

(*
  Compute (decode 14).
  (* = [Dir_right; Dir_right; Dir_right] *)
  Compute (decode 15).
  (* = [Dir_left; Dir_left; Dir_left; Dir_left] *)
  Compute (decode 16).
  (* = [Dir_left; Dir_left; Dir_left; Dir_right] *)
*)

  Lemma encode_decode :
    forall code : nat,
    encode (decode code) = code.
  Proof.
    exact (fun code : nat => proj2_sig (decodable code)).
  Qed.

  Global Opaque decode.

  Lemma decode_encode :
    forall ds : list dir_t,
    decode (encode ds) = ds.
  Proof.
    intro ds. apply encode_inj.
    now rewrite encode_decode with (code := encode ds).
  Qed.

  End INDICES_OF_BINARY_TREES.

  Inductive bintree (Elem : Type) : Type :=
  | BT_null : bintree Elem
  | BT_node (lchild : bintree Elem) (element : Elem) (rchild : bintree Elem) : bintree Elem
  .

  Global Arguments BT_null {Elem}.
  Global Arguments BT_node {Elem}.

  Definition option_elem {Elem : Type} (t : bintree Elem) : option Elem :=
    match t with
    | BT_null => None
    | BT_node t_l t_e t_r => Some t_e
    end
  .

  Definition option_children_pair {Elem : Type} (t : bintree Elem) : option (bintree Elem * bintree Elem) :=
    match t with
    | BT_null => None
    | BT_node t_l t_e t_r => Some (t_l, t_r)
    end
  .

  Definition option_subtree {Elem : Type} : list dir_t -> bintree Elem -> option (bintree Elem) :=
    fix option_subtree_fix (ds : list dir_t) (t : bintree Elem) {struct ds} : option (bintree Elem) :=
    match ds with
    | [] => Some t
    | d :: ds =>
      match t with
      | BT_null => None
      | BT_node t_l t_e t_r => option_subtree_fix ds (@dir_t_rect (fun _ : dir_t => bintree Elem) t_l t_r d)
      end
    end
  .

  Section BINARY_TREE_TO_LIST.

  Polymorphic Definition option2list {A : Type} : option A -> list A :=
    @option_rect A (fun _ => list A) (fun x : A => [x]) []
  .

  Polymorphic Definition pair2list {A : Type} : A * A -> list A :=
    fun pr : A * A =>
    [fst pr; snd pr]
  .

  Context {Elem : Type}.

  Let cnt : bintree Elem -> nat :=
    fix cnt_fix (t : bintree Elem) {struct t} : nat :=
    match t with
    | BT_null => 1
    | BT_node t_l t_e t_r => 1 + cnt_fix t_l + cnt_fix t_r
    end
  .

  Program Fixpoint toList_step (ts : list (bintree Elem)) {measure (list_sum (map cnt ts))} : list Elem :=
    match ts with
    | [] => []
    | BT_null :: ts_tail => toList_step ts_tail
    | BT_node t_l t_e t_r :: ts_tail => t_e :: toList_step ((ts_tail ++ [t_l]) ++ [t_r])
    end.
  Next Obligation.
    unfold Peano.lt.
    do 2 rewrite map_last. do 2 rewrite list_sum_app; cbn.
    do 2 rewrite Nat.add_0_r. rewrite <- Nat.add_assoc at 1.
    rewrite Nat.add_comm; constructor.
  Defined.

  Lemma toList_step_unfold :
    forall ts : list (bintree Elem),
    toList_step ts =
    match ts with
    | [] => []
    | BT_null :: ts_tail => toList_step ts_tail
    | BT_node t_l t_e t_r :: ts_tail => t_e :: toList_step (ts_tail ++ [t_l; t_r])
    end.
  Proof with eauto.
    intros ts. unfold toList_step at 1; rewrite fix_sub_eq.
    - destruct ts as [ | [ | t_l t_e t_r] ts_tail]...
      simpl; apply f_equal.
      replace ((ts_tail ++ [t_l]) ++ [t_r]) with (ts_tail ++ [t_l; t_r]) at 1...
      rewrite <- app_assoc...
    - intros [ | [ | ? ? ?] ?] ? ? ?...
      apply f_equal...
  Qed.

  Global Opaque toList_step.

  Local Open Scope program_scope.

  Definition extract_elements : list (bintree Elem) -> list Elem :=
    flat_map (option2list ∘ option_elem)
  .

  Lemma extract_elements_unfold :
    forall ts : list (bintree Elem),
    extract_elements ts =
    match ts with
    | [] => []
    | BT_null :: ts_tail => extract_elements ts_tail
    | BT_node t_l t_e t_r :: ts_tail => t_e :: extract_elements ts_tail
    end.
  Proof.
    destruct ts as [ | [ | ? ? ?] ?]; reflexivity.
  Qed.

  Definition extract_children : list (bintree Elem) -> list (bintree Elem) :=
    flat_map (@concat (bintree Elem) ∘ option2list ∘ option_map pair2list ∘ option_children_pair)
  .

  Lemma extract_children_unfold :
    forall ts : list (bintree Elem),
    extract_children ts =
    match ts with
    | [] => []
    | BT_null :: ts_tail => extract_children ts_tail
    | BT_node t_l t_e t_r :: ts_tail => [t_l; t_r] ++ extract_children ts_tail
    end.
  Proof.
    destruct ts as [ | [ | ? ? ?] ?]; reflexivity.
  Qed.

  Lemma toList_step_app :
    forall prevs : list (bintree Elem),
    forall nexts : list (bintree Elem),
    toList_step (prevs ++ nexts) =
    extract_elements prevs ++ toList_step (nexts ++ extract_children prevs).
  Proof with eauto with *.
    induction prevs as [ | [ | t_l t_e t_r] prevs IH]; simpl.
    all: intros nexts; autorewrite with list...
    { rewrite toList_step_unfold... }
    { rewrite toList_step_unfold, <- app_assoc, IH, <- app_assoc... }
  Qed.

  Theorem toList_step_spec :
    forall ts : list (bintree Elem),
    toList_step ts =
    extract_elements ts ++ toList_step (extract_children ts).
  Proof.
    intros ts. replace (ts) with (ts ++ []) at 1.
    - exact (toList_step_app ts []).
    - apply app_nil_r.
  Qed.

  Definition toList (root : bintree Elem) : list Elem :=
    toList_step [root]
  .

  End BINARY_TREE_TO_LIST.

End BinaryTrees.
