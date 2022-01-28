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
    fold_left (fun acc : nat => dir_t_rec (fun _ => nat) (2 * acc) (2 * acc + 1)) idx 1
  .

  Lemma encoding_index_last (idx : index_t) (d : dir_t) :
    encoding_index (idx ++ [d]) =
    match d with
    | Dir_left => 2 * encoding_index idx
    | Dir_right => 2 * encoding_index idx + 1
    end.
  Proof.
    unfold encoding_index.
    rewrite fold_left_last.
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

  Inductive bintree (Elem : Type) : Type :=
  | BT_null : bintree Elem
  | BT_node (lchild : bintree Elem) (element : Elem) (rchild : bintree Elem) : bintree Elem
  .

  Global Arguments BT_null {Elem}.
  Global Arguments BT_node {Elem}.

  Definition bintreeExt_view {Elem : Type} : bintree Elem -> index_t -> option Elem :=
    fix bintreeExt_view_fix (t : bintree Elem) (idx : index_t) {struct t} : option Elem :=
    match t with
    | BT_null => None
    | BT_node t_l e t_r =>
      match idx with
      | [] => Some e
      | Dir_left :: idx' => bintreeExt_view_fix t_l idx'
      | Dir_right :: idx' => bintreeExt_view_fix t_r idx'
      end
    end
  .

  Inductive btctx (Elem : Type) : Type :=
  | Ctx_hole : btctx Elem
  | Ctx_left (c_l : btctx Elem) (e : Elem) (t_r : bintree Elem) : btctx Elem
  | Ctx_right (t_l : bintree Elem) (e : Elem) (c_r : btctx Elem) : btctx Elem
  .

  Global Arguments Ctx_hole {Elem}.
  Global Arguments Ctx_left {Elem}.
  Global Arguments Ctx_right {Elem}.

  Definition combine_ctx {Elem : Type} : btctx Elem -> btctx Elem -> btctx Elem :=
    fix combine_ctx_fix (c : btctx Elem) (c' : btctx Elem) : btctx Elem :=
    match c with
    | Ctx_hole => c'
    | Ctx_left c_l e t_r => Ctx_left (combine_ctx_fix c_l c') e t_r
    | Ctx_right t_l e c_r => Ctx_right t_l e (combine_ctx_fix c_r c')
    end
  .

  Lemma combine_ctx_hole_l {Elem : Type} :
    forall c1 : btctx Elem,
    combine_ctx Ctx_hole c1 = c1.
  Proof with eauto.
    reflexivity.
  Qed.

  Lemma combine_ctx_hole_r {Elem : Type} :
    forall c1 : btctx Elem,
    combine_ctx c1 Ctx_hole = c1.
  Proof with eauto.
    induction c1 as [ | c_l IH e t_r | t_l e c_r IH]; simpl...
    all: rewrite IH...
  Qed.

  Lemma combine_ctx_assoc {Elem : Type} :
    forall c1 : btctx Elem,
    forall c2 : btctx Elem,
    forall c3 : btctx Elem,
    combine_ctx c1 (combine_ctx c2 c3) = combine_ctx (combine_ctx c1 c2) c3.
  Proof with eauto.
    induction c1 as [ | c_l IH e t_r | t_l e c_r IH]; simpl...
    - intros c2 c3.
      enough (to_show : (combine_ctx c_l (combine_ctx c2 c3)) = (combine_ctx (combine_ctx c_l c2) c3))...
      rewrite to_show...
    - intros c2 c3.
      enough (to_show : (combine_ctx c_r (combine_ctx c2 c3)) = (combine_ctx (combine_ctx c_r c2) c3))...
      rewrite to_show...
  Qed.

  Inductive btctx_spec {Elem : Type} (sub_t : bintree Elem) : btctx Elem -> bintree Elem -> Prop :=
  | CtxSpec_hole
    : btctx_spec sub_t (Ctx_hole) sub_t
  | CtxSpec_left c_l t_l e t_r
    (H_btctx_spec_l : btctx_spec sub_t c_l t_l)
    : btctx_spec sub_t (Ctx_left c_l e t_r) (BT_node t_l e t_r)
  | CtxSpec_right c_r t_l e t_r
    (H_btctx_spec_r : btctx_spec sub_t c_r t_r)
    : btctx_spec sub_t (Ctx_right t_l e c_r) (BT_node t_l e t_r)
  .

  Lemma btctx_spec_refl {Elem : Type} (root : bintree Elem) :
    btctx_spec root (Ctx_hole) root.
  Proof.
    constructor 1.
  Defined.

  Lemma btctx_spec_trans {Elem : Type} (root : bintree Elem) :
    forall t1 : bintree Elem,
    forall c1 : btctx Elem,
    btctx_spec t1 c1 root ->
    forall t2 : bintree Elem,
    forall c2 : btctx Elem,
    btctx_spec t2 c2 t1 ->
    btctx_spec t2 (combine_ctx c1 c2) root.
  Proof.
    intros t1 c1 X1; induction X1; intros t2 c2 X2; simpl.
    - exact X2.
    - constructor 2; apply IHX1; exact X2.
    - constructor 3; apply IHX1; exact X2.
  Defined.

  Fixpoint run_hole {Elem : Type} (c : btctx Elem) (sub_t : bintree Elem) : bintree Elem :=
    match c with
    | Ctx_hole => sub_t
    | Ctx_left c_l e t_r => BT_node (run_hole c_l sub_t) e t_r
    | Ctx_right t_l e c_r => BT_node t_l e (run_hole c_r sub_t)
    end
  .

  Lemma btctx_spec_run_hole {Elem : Type} :
    forall root : bintree Elem,
    forall c : btctx Elem,
    forall sub_t : bintree Elem,
    btctx_spec sub_t c root <-> run_hole c sub_t = root.
  Proof.
    intros root c sub_t; split.
    - intros X; induction X; simpl.
      + reflexivity.
      + rewrite IHX; reflexivity.
      + rewrite IHX; reflexivity.
    - intros H_eq; subst root; revert sub_t.
      induction c as [ | c_l IH e t_r | t_l e c_r IH]; simpl; intros sub_t.
      + constructor 1.
      + constructor 2; exact (IH sub_t).
      + constructor 3; exact (IH sub_t).
  Qed.

End BinTree.
