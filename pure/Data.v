Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.pure.FunFacts.
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
    fun idx : list dir_t =>
    fold_left (fun code : nat => @dir_t_rec (fun _ : dir_t => nat) (2 * code + 1) (2 * code + 2)) idx 0
  .

  Lemma encode_inj :
    forall idx1 : list dir_t,
    forall idx2 : list dir_t,
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
    {idx : list dir_t | encode idx = code}.
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

  Definition decode : nat -> list dir_t :=
    fun code : nat =>
    proj1_sig (decodable code)
  .

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
    forall idx : list dir_t,
    decode (encode idx) = idx.
  Proof.
    intro idx. apply encode_inj.
    now rewrite encode_decode with (code := encode idx).
  Qed.

  End INDICES_OF_BINARY_TREES.

  Inductive bintree (Elem : Type) : Type :=
  | BT_null : bintree Elem
  | BT_node (lchild : bintree Elem) (element : Elem) (rchild : bintree Elem) : bintree Elem
  .

  Global Arguments BT_null {Elem}.
  Global Arguments BT_node {Elem}.

  Definition option_elem {Elem : Type} : bintree Elem -> option Elem :=
    fun t : bintree Elem =>
    match t with
    | BT_null => None
    | BT_node t_l t_e t_r => Some t_e
    end
  .

  Definition option_children_pair {Elem : Type} : bintree Elem -> option (bintree Elem * bintree Elem) :=
    fun t : bintree Elem =>
    match t with
    | BT_null => None
    | BT_node t_l t_e t_r => Some (t_l, t_r)
    end
  .

  Section BINARY_TREE_ACCESSORIES.

  Polymorphic Definition option2list {A : Type} : option A -> list A :=
    @option_rect A (fun _ => list A) (fun x : A => [x]) []
  .

  Polymorphic Definition pair2list {A : Type} : A * A -> list A :=
    fun pr : A * A =>
    [fst pr; snd pr]
  .

  Context {Elem : Type}.

  Definition option_subtree_init : ((bintree Elem) -> option (bintree Elem)) :=
    fun t => Some t
  .

  Definition option_subtree_step : dir_t -> ((bintree Elem) -> option (bintree Elem)) -> ((bintree Elem) -> option (bintree Elem)) :=
    fun d acc t =>
    match t with
    | BT_null => None
    | BT_node t_l t_e t_r => acc (@dir_t_rect (fun _ => bintree Elem) t_l t_r d)
    end
  .

  Definition option_subtree : list dir_t -> (bintree Elem -> option (bintree Elem)) :=
    fold_right option_subtree_step option_subtree_init
  .

  Lemma option_subtree_unfold idx t :
    option_subtree idx t =
    match idx with
    | [] => Some t
    | d :: idx =>
      match t with
      | BT_null => None
      | BT_node t_l t_e t_r => option_subtree idx (@dir_t_rect (fun _ => bintree Elem) t_l t_r d)
      end
    end.
  Proof. induction idx; eauto. Qed.

  Inductive occurs (t : bintree Elem) : list dir_t -> bintree Elem -> Prop :=
  | Occurs_0 :
    occurs t [] t
  | Occurs_l :
    forall idx : list dir_t,
    forall l : bintree Elem,
    forall e : Elem,
    forall r : bintree Elem,
    occurs t idx l ->
    occurs t (Dir_left :: idx) (BT_node l e r)
  | Occurs_r :
    forall idx : list dir_t,
    forall l : bintree Elem,
    forall e : Elem,
    forall r : bintree Elem,
    occurs t idx r ->
    occurs t (Dir_right :: idx) (BT_node l e r)
  .

  Local Hint Constructors occurs : core.

  Theorem option_subtree_occurs :
    forall t : bintree Elem,
    forall idx : list dir_t,
    forall root : bintree Elem,
    occurs t idx root <-> option_subtree idx root = Some t.
  Proof with discriminate || eauto.
    unfold option_subtree. intros t idx root. split.
    - intros X; induction X...
    - revert t root. induction idx as [ | [ | ] idx IH]; simpl; intros t root H_eq.
      { apply injSome in H_eq; subst root... }
      all: destruct root as [ | l e r]...
  Qed.

  Inductive qtrav_spec : list (bintree Elem) -> list Elem -> Prop :=
  | qtrav_spec1
    : qtrav_spec [] []
  | qtrav_spec2 ts es
    (IH_spec : qtrav_spec ts es)
    : qtrav_spec (BT_null :: ts) es
  | qtrav_spec3 t_l t_e t_r ts es
    (IH_spec : qtrav_spec ((ts ++ [t_l]) ++ [t_r]) es)
    : qtrav_spec (BT_node t_l t_e t_r :: ts) (t_e :: es)
  .

  Local Hint Constructors qtrav_spec : core.

  Definition qtrav :
    { qtrav_body : list (bintree Elem) -> list Elem
    | forall ts : list (bintree Elem), forall xs : list Elem, qtrav_spec ts xs <-> qtrav_body ts = xs
    }.
  Proof with eauto.
    set (cnt :=
      fix cnt_fix (t : bintree Elem) {struct t} : nat :=
      match t with
      | BT_null => 1
      | BT_node t_l t_e t_r => 1 + cnt_fix t_l + cnt_fix t_r
      end
    ).
    set (f := fun ts => list_sum (map cnt ts)).
    set (R := fun ts1 ts2 => f ts1 < f ts2).
    enough (to_show : forall ts, {rslt : list Elem | forall xs, qtrav_spec ts xs <-> rslt = xs}).
    { exists (fun ts => proj1_sig (to_show ts)). exact (fun ts => proj2_sig (to_show ts)). }
    intros ts; pattern ts; revert ts.
    apply FunFacts.well_founded_recursion_with_nat_lt with (get_rank := f) (LT := R)...
    intros [ | [ | t_l t_e t_r] ts] IH.
    - exists ([]); intros xs; split; intros H_spec.
      + inversion H_spec; subst...
      + subst...
    - assert (IH_arg : R ts (BT_null :: ts)).
      { unfold R, f. cbn; constructor. }
      destruct (IH ts IH_arg) as [rslt H_rslt].
      exists (rslt); intros xs; split; intros H_spec.
      + inversion H_spec; subst. apply H_rslt...
      + subst. constructor; apply H_rslt...
    - assert (IH_arg : R ((ts ++ [t_l]) ++ [t_r]) (BT_node t_l t_e t_r :: ts)).
      { unfold R, f. cbn; unfold Peano.lt.
        do 2 rewrite map_last. do 2 rewrite list_sum_app; cbn.
        do 2 rewrite Nat.add_0_r. rewrite <- Nat.add_assoc at 1.
        rewrite Nat.add_comm; constructor.
      }
      destruct (IH ((ts ++ [t_l]) ++ [t_r]) IH_arg) as [rslt H_rslt].
      exists (t_e :: rslt); intros xs; split; intros H_spec.
      + inversion H_spec; subst. apply f_equal, H_rslt...
      + subst. constructor; apply H_rslt...
  Defined.

  Lemma qtrav_unfold queue :
    proj1_sig qtrav queue =
    match queue with
    | [] => []
    | BT_null :: queue_tail => proj1_sig qtrav queue_tail
    | BT_node t_l t_e t_r :: queue_tail => t_e :: proj1_sig qtrav ((queue_tail ++ [t_l]) ++ [t_r])
    end.
  Proof with eauto.
    destruct qtrav as [qtrav_body H_qtrav_body]; simpl.
    destruct queue as [ | [ | t_l t_e t_r] queue_tail]; simpl; apply H_qtrav_body...
    all: constructor; apply H_qtrav_body...
  Qed.

  Definition toList_step := proj1_sig qtrav.

  Lemma toList_step_unfold ts :
    toList_step ts =
    match ts with
    | [] => []
    | BT_null :: ts_tail => toList_step ts_tail
    | BT_node t_l t_e t_r :: ts_tail => t_e :: toList_step (ts_tail ++ [t_l; t_r])
    end.
  Proof with eauto.
    unfold toList_step; rewrite qtrav_unfold with (queue := ts) at 1.
    destruct ts as [ | [ | t_l t_e t_r] ts_tail]...
    rewrite <- app_assoc at 1; replace ([t_l] ++ [t_r]) with ([t_l; t_r])...
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

  End BINARY_TREE_ACCESSORIES.

End BinaryTrees.
