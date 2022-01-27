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

  Inductive index_t : Set :=
  | Nil_op : index_t
  | Cons_op : index_t -> dir_t -> index_t
  .

  Fixpoint encoding_index (idx : index_t) {struct idx} : nat :=
    match idx with
    | Nil_op => 1
    | Cons_op idx Dir_left => 2 * encoding_index idx
    | Cons_op idx Dir_right => 2 * encoding_index idx + 1
    end
  .

  Lemma decoding_index :
    forall code : nat,
    code <> 0 ->
    {idx : index_t | encoding_index idx = code}.
  Proof with lia || eauto.
    strong_rec. intros [ | n']; [contradiction | set (n := S n')].
    destruct n' as [ | n'']; intros acc_hyp H_n_ne_0.
    - exists (Nil_op)...
    - assert (claim1 := Nat.div_mod n 2 (S_eq_0_elim 1)).
      destruct (Nat.mod_bound_pos n 2 (le_intro_0_le_n n) (le_S 1 1 (le_n 1))) as [claim2 claim3].
      assert (claim4 : leq (n / 2) n).
      { apply le_implies_leq... }
      assert (claim5 : n / 2 <> n)...
      assert (claim6 : n / 2 <> 0)...
      destruct (acc_hyp (n / 2) claim4 claim5 claim6) as [idx H_idx].
      destruct (n mod 2) as [ | [ | n_mod_2]] eqn: H_obs...
      { exists (Cons_op idx Dir_left); simpl... }
      { exists (Cons_op idx Dir_right); simpl... }
  Qed.

  Lemma encoding_index_range :
    forall code : nat,
    (exists idx : index_t, encoding_index idx = code) <-> code <> 0.
  Proof with lia || eauto.
    intros n; split.
    - intros [idx H_idx]; subst n; induction idx as [ | idx IH [ | ]]; simpl...
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
    induction idx1 as [ | idx1 IH [ | ]]; intros [ | idx2 [ | ]]; simpl...
    - pose (claim1 idx2)...
    - intros H_eq; rewrite (IH idx2)...
    - pose (claim1 idx1)...
    - intros H_eq; rewrite (IH idx2)...
  Qed.

  Section INDEX_ORDERING.

  Local Instance list_dir_isPoset : isPoset (list dir_t) :=
    list_isPoset_wrt_lex_le
    dir_compare
    dir_compare_spec_LT
    dir_compare_spec_EQ
    dir_compare_spec_GT
  .

  Fixpoint index_to_list (idx : index_t) {struct idx} : list dir_t :=
    match idx with
    | Nil_op => []
    | Cons_op idx d => index_to_list idx ++ [d]
    end
  .

  Lemma index_to_list_inj :
    forall idx1 : index_t,
    forall idx2 : index_t,
    index_to_list idx1 = index_to_list idx2 ->
    idx1 = idx2.
  Proof with eauto.
    induction idx1 as [ | idx1 IH d1]; destruct idx2 as [ | idx2 d2]; simpl; intros H_eq...
    - contradiction (app_cons_not_nil (index_to_list idx2) [] d2 H_eq).
    - contradiction (app_cons_not_nil (index_to_list idx1) [] d1 (eq_symmetry _ _ H_eq)).
    - apply last_inj in H_eq.
      destruct H_eq as [H_eq1 H_eq2]; subst d2.
      rewrite IH with (idx2 := idx2)...
  Qed.

  Definition index_eq : index_t -> index_t -> Prop :=
    fun idx1 : index_t =>
    fun idx2 : index_t =>
    lex_eq dir_compare (index_to_list idx1) (index_to_list idx2)
  .

  Lemma index_eq_iff :
    forall idx1 : index_t,
    forall idx2 : index_t,
    index_eq idx1 idx2 <-> idx1 = idx2.
  Proof with eauto.
    unfold index_eq, lex_eq; intros idx1 idx2; split; intros H_eq.
    - apply index_to_list_inj, dir_list_compare_Eq...
    - subst idx2. apply dir_list_compare_Eq...
  Qed.

  Local Instance index_eq_Equivalence :
    Equivalence index_eq.
  Proof with eauto.
    unfold index_eq; split.
    - intros idx1; apply index_eq_iff...
    - intros idx1 idx2 H_eq1; apply index_eq_iff; symmetry; apply index_eq_iff...
    - intros idx1 idx2 idx3 H_eq1 H_eq2; apply index_eq_iff; transitivity (idx2); apply index_eq_iff...
  Qed.

  Definition index_le : index_t -> index_t -> Prop :=
    fun idx1 : index_t =>
    fun idx2 : index_t =>
    index_to_list idx1 =< index_to_list idx2
  .

  Local Instance index_le_PreOrder :
    PreOrder index_le.
  Proof with eauto with *.
    unfold index_le; split.
    - intros idx1...
    - intros idx1 idx2 idx3...
  Qed.

  Local Instance index_le_PartialOrder :
    PartialOrder index_eq index_le.
  Proof with eauto with *.
    assert (claim1 := lex_le_PartialOrder dir_compare dir_compare_spec_LT dir_compare_spec_EQ dir_compare_spec_GT).
    unfold index_le, index_eq; intros idx1 idx2; split; unfold Basics.flip.
    - intros H_eq; split; rewrite H_eq...
    - intros [H_le H_ge].
      exact (proj2 (claim1 (index_to_list idx1) (index_to_list idx2)) (conj H_le H_ge))...
  Qed.

  Global Instance index_isPoset : isPoset index_t :=
    { leProp := index_le
    ; Poset_requiresSetoid := {| eqProp := index_eq; Setoid_requiresEquivalence := index_eq_Equivalence |}
    ; Poset_requiresPreOrder := index_le_PreOrder
    ; Poset_requiresPartialOrder := index_le_PartialOrder
    }
  .

  End INDEX_ORDERING.

  End INDICES_OF_BINARY_TREES.

  Section BINARY_TREES.

  Variable Elem : Set.

  Inductive bintree : Set :=
  | BT_null : bintree
  | BT_node (lchild : bintree) (element : Elem) (rchild : bintree) : bintree
  .

  End BINARY_TREES.

  Global Arguments bintree {Elem}.

End BinTree.
