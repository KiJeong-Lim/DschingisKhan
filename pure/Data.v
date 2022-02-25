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

  Section LIST_EXTENSIONALITY.

  Definition good_idx_implies_nth_error_ne_None {A : Type} (xs : list A) :
    forall idx : nat,
    idx < length xs ->
    nth_error xs idx <> None.
  Proof.
    induction xs as [ | x xs IH].
    - intros idx H_lt.
      exact (lt_elim_n_lt_0 idx H_lt).
    - intros [ | idx'] H_lt.
      + exact (Some_ne_None x).
      + simpl in *.
        apply IH.
        exact (lt_elim_S_n_lt_S_m idx' (length xs) H_lt).
  Defined.

  Definition listEXT_view {A : Type} (xs : list A) : forall idx : nat, {ret : option A | idx < length xs -> ret <> None} :=
    fun idx : nat =>
    exist _ (nth_error xs idx) (good_idx_implies_nth_error_ne_None xs idx)
  .

  Definition listExt_view {A : Type} (xs : list A) : nat -> option A :=
    fun idx : nat =>
    proj1_sig (listEXT_view xs idx)
  .

  Lemma list_extensionality {A : Type} :
    forall xs1 : list A,
    forall xs2 : list A,
    xs1 = xs2 <-> (forall n : nat, listExt_view xs1 n = listExt_view xs2 n).
  Proof with discriminate || eauto.
    cbn.
    induction xs1 as [ | x1 xs1 IH]; intros [ | x2 xs2]; simpl; split...
    - intros H_false.
      contradiction (Some_ne_None x2).
      symmetry; exact (H_false 0).
    - intros H_false.
      contradiction (Some_ne_None x1).
      exact (H_false 0).
    - intros H_eq.
      rewrite H_eq.
      reflexivity.
    - intros H_eq.
      assert (claim1 := H_eq 0).
      simpl in claim1; apply Some_inj in claim1; subst x2.
      apply eq_congruence, IH.
      exact (fun n => H_eq (S n)).
  Qed.

  Lemma listExt_map {A : Type} {B : Type} (f : A -> B) (xs : list A) :
    (forall n : nat, listExt_view (map f xs) n = (fmapMaybe f) (listExt_view xs n)).
  Proof with discriminate || eauto.
    cbn.
    induction xs as [ | x xs IH]; simpl.
    - intros [ | n']...
    - intros [ | n']; simpl...
  Qed.

  Definition safeLookat {A : Type} (xs : list A) : forall idx : nat, idx < length xs -> A :=
    fun idx : nat =>
    match listEXT_view xs idx with
    | exist _ xr H_xr => fun H_idx : idx < length xs => fromJust xr (H_xr H_idx)
    end
  .

  Lemma listExt_safeLookat {A : Type} (xs : list A) :
    forall n : nat,
    listExt_view xs n =
    match n_le_m_or_m_lt_n_holds_for_any_n_and_any_m (length xs) n with
    | left H_le => None
    | right H_lt => Some (safeLookat xs n H_lt)
    end.
  Proof with eauto.
    intros n; cbn.
    destruct (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m (length xs)) as [H_le | H_lt].
    - apply nth_error_None...
    - apply (proj2 (fromJust_spec (nth_error xs n) (fromJust (nth_error xs n) (good_idx_implies_nth_error_ne_None xs n H_lt))))...
  Qed.

  End LIST_EXTENSIONALITY.

  Section LIST_SWAP.

  Context {A : Type}.

  Definition addIndices_aux : list A -> nat -> list (A * nat) :=
    fold_right (fun x : A => fun acc : nat -> list (A * nat) => fun n : nat => (x, n) :: acc (1 + n)) (fun n : nat => [])
  .

  Lemma addIndices_aux_unfold :
    forall xs : list A,
    forall n : nat,
    addIndices_aux xs n =
    match xs with
    | [] => []
    | hd_xs :: tl_xs => (hd_xs, n) :: addIndices_aux tl_xs (S n)
    end.
  Proof with eauto.
    induction xs as [ | x xs IH]; simpl...
  Qed.

  Definition addIndices (xs : list A) : list (A * nat) :=
    addIndices_aux xs 0
  .

  Lemma addIndices_unfold :
    forall xs : list A,
    addIndices xs =
    match xs with
    | [] => []
    | hd_xs :: tl_xs => (hd_xs, 0) :: map (fun it => (fst it, 1 + snd it)) (addIndices tl_xs)
    end.
  Proof with eauto.
    unfold addIndices; cbn.
    intros xs1; generalize 0 as n; intros n.
    rewrite addIndices_aux_unfold at 1.
    destruct xs1 as [ | x1 xs1]...
    apply eq_congruence.
    clear x1; revert n; induction xs1 as [ | x1 xs1 IH]; simpl...
    intros n; apply eq_congruence; exact (IH (S n)).
  Qed.

  Lemma addIndices_length :
    forall xs : list A,
    length (addIndices xs) = length xs.
  Proof with eauto.
    induction xs as [ | x xs IH]...
    rewrite addIndices_unfold; simpl...
    apply eq_congruence; rewrite map_length...
  Qed.

  Lemma addIndices_map_fst :
    forall xs : list A,
    map fst (addIndices xs) = xs.
  Proof with eauto.
    induction xs as [ | x xs IH]...
    rewrite addIndices_unfold; simpl.
    apply eq_congruence.
    rewrite <- IH at 2.
    generalize (addIndices xs) as its.
    clear x xs IH.
    induction its; simpl...
    apply eq_congruence...
  Qed.

  Lemma addIndices_map_snd :
    forall xs : list A,
    forall idx : nat,
    idx < length xs <-> nth_error (map snd (addIndices xs)) idx = Some idx.
  Proof with eauto.
    intros xs idx; split.
    { unfold addIndices; replace idx with (0 + idx) at 3...
      generalize 0 as n; revert idx; induction xs as [ | x xs IH]; simpl; intros i n H_lt.
      - exact (lt_elim_n_lt_0 i H_lt).
      - destruct i as [ | i']; simpl.
        + apply eq_congruence; lia.
        + apply lt_elim_S_n_lt_S_m in H_lt.
          rewrite (IH i' (S n) H_lt).
          apply eq_congruence; lia.
    }
    { intros H_Some.
      rewrite <- addIndices_length, <- (map_length snd).
      apply nth_error_Some.
      rewrite H_Some.
      discriminate.
    }
  Qed.

  Lemma listExt_addIndices (xs : list A) :
    forall idx : nat,
    match listExt_view (addIndices xs) idx with
    | None => idx >= length xs
    | Some (x, n) => listExt_view xs idx = Some x /\ idx = n
    end.
  Proof with discriminate || eauto.
    intros idx; cbn.
    destruct (nth_error (addIndices xs) idx) as [[x n] | ] eqn: H_obs_addIndices.
    - assert (H_nth : nth idx (addIndices xs) (x, n) = (x, n)) by now apply nth_error_nth.
      assert (claim1 := (map_nth fst (addIndices xs) (x, n) idx)).
      assert (claim2 := (map_nth snd (addIndices xs) (x, n) idx)).
      rewrite H_nth in claim1, claim2; cbn in claim1, claim2.
      rewrite addIndices_map_fst in claim1.
      assert (H_length : idx < length xs).
      { rewrite <- addIndices_length. apply nth_error_Some. rewrite H_obs_addIndices... }
      assert (H_n_eq_idx := proj1 (addIndices_map_snd xs idx) H_length).
      apply nth_error_nth with (d := n) in H_n_eq_idx.
      rewrite claim2 in H_n_eq_idx.
      split... rewrite <- claim1; apply nth_error_nth'...
    - rewrite <- addIndices_length; apply nth_error_None...
  Qed.

  Definition listSwap_aux (xs : list A) (idx1 : nat) (idx2 : nat) (default_val : A) (idx : nat) : A :=
    let x1 : A := maybe default_val id (nth_error xs idx1) in
    let x2 : A := maybe default_val id (nth_error xs idx2) in
    if eq_dec_nat idx idx1 then x2 else
    if eq_dec_nat idx idx2 then x1 else
    default_val
  .

  Definition listSwap (idx1 : nat) (idx2 : nat) : list A -> list A :=
    fun xs : list A =>
    map (uncurry (listSwap_aux xs idx1 idx2)) (addIndices xs)
  .

  Lemma listSwap_length :
    forall idx1 : nat,
    forall idx2 : nat,
    forall xs : list A,
    length (listSwap idx1 idx2 xs) = length xs.
  Proof.
    unfold listSwap; intros idx1 idx2 xs.
    transitivity (length (addIndices xs)); [apply map_length | apply addIndices_length].
  Qed.

  Lemma listExt_swap :
    forall idx1 : nat,
    forall idx2 : nat,
    forall xs : list A,
    forall idx : nat,
    listExt_view (listSwap idx1 idx2 xs) idx =
    fmapMaybe (uncurry (listSwap_aux xs idx1 idx2)) (listExt_view (addIndices xs) idx).
  Proof.
    intros idx1 idx2 xs idx.
    exact (listExt_map (uncurry (listSwap_aux xs idx1 idx2)) (addIndices xs) idx).
  Qed.

  Theorem listSwap_main_spec :
    forall xs : list A,
    forall idx1 : nat,
    forall val1 : A,
    listExt_view xs idx1 = Some val1 ->
    forall idx2 : nat,
    forall val2 : A,
    listExt_view xs idx2 = Some val2 ->
    forall idx : nat,
    forall val : A,
    listExt_view xs idx = Some val ->
    match listExt_view (listSwap idx1 idx2 xs) idx with
    | None => False
    | Some x => x =
      if eq_dec_nat idx idx1 then val2 else
      if eq_dec_nat idx idx2 then val1 else
      val
    end.
  Proof with discriminate || eauto.
    cbn; intros xs idx1 val1 H_idx1 idx2 val2 H_idx2 idx val H_idx.
    assert (claim1 := listExt_swap idx1 idx2 xs idx).
    assert (claim2 := listExt_addIndices xs idx).
    cbn in claim1, claim2; rewrite claim1.
    unfold fmapMaybe, listExt_view, listSwap_aux; simpl.
    destruct (nth_error (addIndices xs) idx) as [[x n] |] eqn: H_obs_addIndices; simpl in *.
    - destruct claim2 as [H_obs_xs H_obs_idx]; subst n.
      destruct (eq_dec_nat idx idx1) as [H_yes1 | H_no1].
      { subst idx. rewrite H_idx2... }
      destruct (eq_dec_nat idx idx2) as [H_yes2 | H_no2].
      { subst idx. rewrite H_idx1... }
      congruence.
    - apply nth_error_None in claim2; rewrite claim2 in H_idx...
  Qed.

  End LIST_SWAP.

End LinkedLists.

Module BinaryTrees.

(*Import ListNotations EqFacts MyUtilities BasicSetoidTheory BasicPosetTheory LinkedLists.

  Local Open Scope program_scope.

  Section INDICES_OF_BINARY_TREES.

  Inductive dir_t : Set := Dir_left : dir_t | Dir_right : dir_t.

  Definition index_t : Set := list dir_t.

  Definition encode (idx : index_t) := fold_left (fun code : nat => @dir_t_rec (fun _ : dir_t => nat) (2 * code + 1) (2 * code + 2)) idx 0.

  Lemma encode_inj :
    forall idx1 : index_t,
    forall idx2 : index_t,
    encode idx1 = encode idx2 ->
    idx1 = idx2.
  Proof with lia || eauto.
    unfold encode. intros idx1 idx2. do 2 rewrite <- fold_left_rev_right.
    intros H_eq. apply list_rev_inj. revert H_eq.
    generalize (rev idx2) as ds2. generalize (rev idx1) as ds1. clear idx1 idx2.
    set (myF := fold_right (fun d : dir_t => fun code : nat => @dir_t_rec (fun _ : dir_t => nat) (2 * code + 1) (2 * code + 2) d) 0).
    induction ds1 as [ | d1 ds1 IH]; destruct ds2 as [ | d2 ds2]; simpl...
    - destruct d2; simpl dir_t_rec...
    - destruct d1; simpl dir_t_rec...
    - destruct d1; destruct d2; simpl dir_t_rec...
      all: intros H_eq; assert (claim1 : myF ds1 = myF ds2)...
      all: apply eq_congruence...
  Qed.

  Lemma decodable :
    forall code : nat,
    {idx : index_t | encode idx = code}.
  Proof with lia || eauto.
    induction code as [[ | code'] IH] using Wf_nat.lt_wf_rec.
    - exists ([])...
    - set (code := S code').
      destruct (code mod 2) as [ | [ | code_mod_2]] eqn: H_obs.
      + assert (claim1 : code = 2 * ((code - 2) / 2) + 2).
        { apply (positive_even code ((code - 2) / 2))... }
        assert (claim2 : (code - 2) / 2 < code)...
        destruct (IH ((code - 2) / 2) claim2) as [idx H_idx].
        exists (idx ++ [Dir_right]).
        unfold encode. rewrite fold_left_last. unfold dir_t_rec at 1.
        unfold encode in H_idx. rewrite H_idx...
      + assert (claim1 : code = 2 * ((code - 1) / 2) + 1).
        { apply (positive_odd code ((code - 1) / 2))... }
        assert (claim2 : (code - 1) / 2 < code)...
        destruct (IH ((code - 1) / 2) claim2) as [idx H_idx].
        exists (idx ++ [Dir_left]).
        unfold encode. rewrite fold_left_last. unfold dir_t_rec at 1.
        unfold encode in H_idx. rewrite H_idx...
      + pose (Nat.mod_bound_pos code 2)...
  Defined.

  Definition decode code : index_t := proj1_sig (decodable code).

(* (* Example "decode" *)
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
    forall idx : index_t,
    decode (encode idx) = idx.
  Proof.
    intro idx. apply encode_inj.
    now rewrite encode_decode with (code := encode idx).
  Qed.

  Global Program Instance index_t_isPoset : isPoset index_t :=
    { Poset_requiresSetoid :=
      {| eqProp := @eq index_t; Setoid_requiresEquivalence := @eq_equivalence index_t |}
    ; leProp := fun idx1 idx2 => encode idx1 <= encode idx2
    }
  .
  Next Obligation with eauto with *.
    split...
  Qed.
  Next Obligation with eauto with *.
    intros idx1 idx2; cbn. unfold flip; split.
    - intros ?; subst...
    - intros [H_le H_ge]. apply encode_inj...
  Qed.

  End INDICES_OF_BINARY_TREES.

  Inductive bintree (Elem : Type) : Type :=
  | BT_null : bintree Elem
  | BT_node (lchild : bintree Elem) (element : Elem) (rchild : bintree Elem) : bintree Elem
  .

  Global Arguments BT_null {Elem}.
  Global Arguments BT_node {Elem}.

  Polymorphic Definition option2list {A : Type} : option A -> list A :=
    @option_rect A (fun _ => list A) (fun x : A => [x]) []
  .

  Polymorphic Definition pair2list {A : Type} : A * A -> list A :=
    fun '(x1, x2) => [x1; x2]
  .

  Section BINARYTREE_BASIC_OPERATIONS.

  Context {Elem : Type}.

  Definition option_elem t : option Elem :=
    match t with
    | BT_null => None
    | BT_node t_l t_e t_r => Some t_e
    end
  .

  Definition option_children_pair t : option (bintree Elem * bintree Elem) :=
    match t with
    | BT_null => None
    | BT_node t_l t_e t_r => Some (t_l, t_r)
    end
  .

  Definition option_subtree_init t : option (bintree Elem) := Some t.

  Definition option_subtree_step d acc t : option (bintree Elem) :=
    match t with
    | BT_null => None
    | BT_node t_l t_e t_r => acc (@dir_t_rect (fun _ => bintree Elem) t_l t_r d)
    end
  .

  Definition option_subtree : index_t -> bintree Elem -> option (bintree Elem) :=
    fix option_subtree_fix (idx : list dir_t) (t : bintree Elem) {struct idx} : option (bintree Elem) :=
    match idx with
    | [] => Some t
    | d :: idx =>
      match t with
      | BT_null => None
      | BT_node t_l t_e t_r => option_subtree_fix idx (@dir_t_rect (fun _ : dir_t => bintree Elem) t_l t_r d)
      end
    end
  .

  Definition extract_elements := flat_map (option2list ∘ option_elem).

  Definition extract_children := flat_map (@concat (bintree Elem) ∘ option2list ∘ option_map pair2list ∘ option_children_pair).

  Inductive occurs t : index_t -> bintree Elem -> Prop :=
  | Occurs_0
    : occurs t [] t
  | Occurs_l ds l e r
    (H_l : occurs t ds l)
    : occurs t (Dir_left :: ds) (BT_node l e r)
  | Occurs_r ds l e r
    (H_r : occurs t ds r)
    : occurs t (Dir_right :: ds) (BT_node l e r)
  .

  Local Hint Constructors occurs : core.

  Lemma occurs_iff t ds root :
    occurs t ds root <->
    option_subtree ds root = Some t.
  Proof with discriminate || eauto.
    split. intros X; induction X... revert t root.
    induction ds as [ | [ | ] ds IH]; simpl; intros t root H_eq.
    { apply injSome in H_eq; subst... }
    all: destruct root as [ | l e r]...
  Qed.

  Fixpoint getRank (t : bintree Elem) : nat :=
    match t with
    | BT_null => 0
    | BT_node t_l t_e t_r => 1 + max (getRank t_l) (getRank t_r)
    end
  .

  Definition toList root : list Elem := flat_map option2list (map (fun idx => maybe None option_elem (option_subtree (decode idx) root)) (seq 0 (2 ^ getRank root - 1))).

  End BINARYTREE_BASIC_OPERATIONS.
*)

End BinaryTrees.
